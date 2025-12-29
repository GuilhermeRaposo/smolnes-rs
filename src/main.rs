#![allow(static_mut_refs)]
use sdl2_sys::SDL_CreateRenderer;
use sdl2_sys::SDL_CreateTexture;
use sdl2_sys::SDL_CreateWindow;
use sdl2_sys::SDL_Scancode;
use sdl2_sys::SDL_RWread;
use sdl2_sys::SDL_RWFromFile;
use sdl2_sys::SDL_INIT_VIDEO;
use sdl2_sys::SDL_WindowFlags::SDL_WINDOW_SHOWN;
use sdl2_sys::SDL_PixelFormatEnum::SDL_PIXELFORMAT_BGR565;
use sdl2_sys::SDL_TextureAccess::SDL_TEXTUREACCESS_STREAMING;
use sdl2_sys::SDL_RendererFlags::SDL_RENDERER_PRESENTVSYNC;
use sdl2_sys::SDL_UpdateTexture;
use sdl2_sys::SDL_RenderCopy;
use sdl2_sys::SDL_RenderPresent;
use sdl2_sys::SDL_PollEvent;
use sdl2_sys::SDL_Event;
use sdl2_sys::SDL_EventType::SDL_QUIT;
use std::env;
use std::os::raw::c_void;

static mut rom: *const u8 = std::ptr::null();
static mut chrrom: *mut u8 = std::ptr::null_mut();                // Points to the start of PRG/CHR ROM
static mut prg:[u8; 4] = [0; 4];
static mut chr:[u8; 8] = [0; 8];             // Current PRG/CHR banks
static mut prgbits: u8 = 14;
static mut chrbits: u8 = 12;       // Number of bits per PRG/CHR bank
static mut A: u8 = 0;
static mut X: u8 = 0;
static mut Y: u8 = 0;
static mut P: u8 = 4;
static mut S: u8 = 0xFD;
static mut PCH: u8 = 0;
static mut PCL: u8 = 0; // CPU Registers
static mut addr_lo: u8 = 0;
static mut addr_hi: u8 = 0;                 // Current instruction address
static mut nomem: u8 = 0;  // 1 => current instruction doesn't write to memory
static mut result: u8 = 0; // Temp variable
static mut val: u8 = 0;    // Current instruction value
static mut cross: u8 = 0;  // 1 => page crossing occurred
static mut tmp: u8 = 0;    // Temp variables
static mut ppumask: u8 = 0;
static mut ppuctrl: u8 = 0;
static mut ppustatus: u8 = 0; // PPU registers
static mut ppubuf: u8 = 0;                      // PPU buffered reads
static mut W: u8 = 0;                           // Write toggle PPU register
static mut fine_x: u8 = 0;                      // X fine scroll offset, 0..7
static mut opcode: u8 = 0;                      // Current instruction opcode
static mut nmi_irq: u8 = 0;              // 1 => IRQ occurred
                                 // 4 => NMI occurred
static mut ntb: u8 = 0;                         // Nametable byte
static mut ptb_lo: u8 = 0;                     // Pattern table lowbyte
static mut vram:[u8; 2048] = [0; 2048];             // Nametable RAM
static mut palette_ram:[u8; 64] = [0; 64];            // Palette RAM
static mut ram:[u8; 8192] = [0; 8192];                   // CPU RAM
static mut chrram:[u8; 8192] = [0; 8192];                // CHR RAM (only used for some games)
static mut prgram:[u8; 8192] = [0; 8192];                // PRG RAM (only used for some games)
static mut oam:[u8; 256] = [0; 256];                    // Object Attribute Memory (sprite RAM)
static mut mask:[u8; 20] = [128, 64, 1, 2,     // Masks used in branch instructions
                            1,   0,  0, 1, 4, 0, 0, 4, 0,
                            0,   64, 0, 8, 0, 0, 8]; // Masks used in SE*/CL* instructions.
static mut keys: u8 = 0;                              // Joypad shift register
static mut mirror: u8 = 0;                            // Current mirroring mode
static mut mmc1_bits: u8 = 0;
static mut mmc1_data: u8 = 0;
static mut mmc1_ctrl: u8 = 0;   // Mapper 1 (MMC1) registers
static mut mmc3_chrprg:[u8; 8] = [0; 8];
static mut mmc3_bits: u8 = 0;         // Mapper 4 (MMC3) registers
static mut mmc3_irq: u8 = 0;
static mut mmc3_latch: u8 = 0;              //
static mut chrbank0: u8 = 0;
static mut chrbank1: u8 = 0;
static mut prgbank: u8 = 0;       // Current PRG/CHR bank
static mut rombuf:[u8; 1024 * 1024] = [0; 1024 * 1024];               // Buffer to read ROM file into
static mut key_state: *mut u8 = std::ptr::null_mut();

static mut scany: u16 = 0;          // Scanline Y
static mut T: u16 = 0;
static mut V: u16 = 0;                // "Loopy" PPU registers
static mut sum: u16 = 0;                 // Sum used for ADC/SBC
static mut dot: u16 = 0;                 // Horizontal position of PPU, from 0..340
static mut atb: u16 = 0;                 // Attribute byte
static mut shift_hi: u16 = 0;
static mut shift_lo: u16 = 0;  // Pattern table shift registers
static mut cycles: u16 = 0;              // Cycle count for current instruction
static mut frame_buffer:[u16; 61440] = [0; 61440]; // 256x240 pixel frame buffer. Top and bottom 8 rows
                         // are not drawn.

static mut shift_at: u32 = 0;
static mut abc: u32 = 1;

fn pull() -> u8 {
    unsafe {
        S = S.wrapping_add(1);
        return mem(S, 1, 0, 0);
    }
}

fn push(x: u8) -> u8 {
    unsafe {
        let r = mem(S, 1, x, 1);
        S = S.wrapping_sub(1);
        return r;
    }
}

// Read a byte from CHR ROM or CHR RAM.
unsafe fn get_chr_byte(a: u16) -> *mut u8 {
    unsafe {
        let index = (chr[(a >> chrbits) as usize] as usize) << chrbits
                    | (a as usize % (1 << chrbits));
        chrrom.add(index)
    }
}


// Read a byte from nametable RAM.
unsafe fn get_nametable_byte(a: u16) -> *mut u8 {
    unsafe {
        let index = match mirror {
            0 => (a % 1024) as usize,                 // single bank 0
            1 => (a % 1024 + 1024) as usize,          // single bank 1
            2 => (a & 2047) as usize,                 // vertical mirroring
            _ => ((a / 2 & 1024) | (a % 1024)) as usize, // horizontal mirroring
        };
    
        vram.as_mut_ptr().add(index)
    }
}


// If `write` is non-zero, writes `_val` to the address `hi:lo`, otherwise reads
// a value from the address `hi:lo`.
fn mem(mut lo: u8, mut hi: u8, _val: u8, write: u8) -> u8 {
    unsafe {
        let mut addr: u16 = (hi as u16) << 8 | lo as u16;

        hi >>= 4;
        match hi {
            0 | 1 => { // $0000...$1fff RAM
                if write != 0 {
                    ram[addr as usize] = _val;
                    return _val;
                } else {
                    return ram[addr as usize];
                }
            } 

            2 | 3 => { // $2000..$2007 PPU (mirrored)
                lo &= 7;

                // read/write $2007
                if lo == 7 {
                    tmp = ppubuf;
                    let _rom: *mut u8 =
                        // Access CHR ROM or CHR RAM
                        if V < 8192 {
                            if write != 0 && chrrom != chrram.as_mut_ptr() {
                                &mut tmp
                            }
                            else {
                                get_chr_byte(V)
                            }
                        }
                        else {
                            // Access nametable RAM
                            if V < 16128 {
                                get_nametable_byte(V)
                            }
                            else {
                                // Access palette RAM
                                palette_ram.as_mut_ptr().offset(if (V & 19) == 16 {
                                    ((V ^ 16) & 0xFF) as isize  // Truncate to 8 bits
                                } else {
                                    (V & 0xFF) as isize  // Truncate to 8 bits
                                })
                            }
                        };
                                    
                    if write != 0 {
                        *_rom = _val;
                    } else {
                        ppubuf = *_rom;
                    }
                    V += if ppuctrl & 4 != 0 {
                        32
                    }
                    else {
                        1
                    };
                    V %= 16384;
                    return tmp;
                }

                if write != 0 {
                    match lo {
                        0 => { // $2000 ppuctrl
                            ppuctrl = _val;
                            T = T & 0xf3ff | _val as u16 % 4 << 10;
                        }
                        1 => {  // $2001 ppumask
                            ppumask = _val;
                        }
                        5 => { // $2005 ppuscroll
                            W ^= 1;
                            T = if W != 0 {
                                fine_x = _val & 7;
                                (T & !31) | (_val as u16 / 8)
                            } else {
                                (T & 0x8c1f) | ((_val as u16 % 8) << 12) | ((_val as u16 * 4) & 0x3e0)
                            };
                        }
                        6 => { // $2006 ppuaddr
                            W ^= 1;
                            T = if W != 0 {
                                (T & 0xff) | ((_val as u16 % 64) << 8)
                            } else {
                                V = T & !0xff | _val as u16;
                                V
                            };
                        }
                        _ => {}
                    }
                }

                if lo == 2 { // $2002 ppustatus
                    tmp = ppustatus & 0xe0;
                    ppustatus &= 0x7f;
                    W = 0;
                    return tmp;
                }
            } 



            4 => {
                if write != 0 && lo == 20 { // $4014 OAM DMA
                    for i in (0..256).rev() {
                        oam[i] = mem(i as u8, _val, 0, 0);
                    }

                }
                
                // $4016 Joypad 1
                tmp = 0;
                hi = 8;
                while hi > 0 {
                    hi -= 1;
                    tmp = tmp * 2 +
                        *key_state.add([
                            SDL_Scancode::SDL_SCANCODE_X,      // A
                            SDL_Scancode::SDL_SCANCODE_Z,      // B
                            SDL_Scancode::SDL_SCANCODE_TAB,    // Select
                            SDL_Scancode::SDL_SCANCODE_RETURN, // Start
                            SDL_Scancode::SDL_SCANCODE_UP,     // Dpad Up
                            SDL_Scancode::SDL_SCANCODE_DOWN,   // Dpad Down
                            SDL_Scancode::SDL_SCANCODE_LEFT,   // Dpad Left
                            SDL_Scancode::SDL_SCANCODE_RIGHT,  // Dpad Right
                        ][hi as usize] as usize);
                }
                if lo == 22 {
                if write != 0 {
                    keys = tmp;
                } else {
                    tmp = keys & 1;
                    keys /= 2;
                    return tmp;
                }
                }
                return 0;
            }

            6 | 7 => { // $6000...$7fff PRG RAM
                addr &= 8191;
                return if write != 0 {
                    prgram[addr as usize] = _val;
                    _val
                }
                else {
                    prgram[addr as usize]
                }
            }

            _ => { // $8000...$ffff ROM
                // handle mapper writes
                if write != 0 {
                    match rombuf[6] >> 4 {
                        7 => { // mapper 7
                            mirror = !(_val / 16);
                            prg[0] = _val % 8 * 2;
                            prg[1] = prg[0] + 1;
                        }
                        4 => { // mapper 4
                            let addr1: u8 = (addr & 1) as u8;
                            match hi >> 1 {
                                4 => { // Bank select/bank data
                                    if addr1 != 0 {
                                        mmc3_chrprg[(mmc3_bits & 7) as usize] = _val;
                                    } else {
                                        mmc3_bits = _val;
                                    }
                                    tmp = mmc3_bits >> 5 & 4;
                                    for i in (0..4).rev() {
                                        chr[(0 + i + tmp) as usize] = (mmc3_chrprg[(i / 2) as usize] & !1) | (i & 1);
                                        chr[(4 + i - tmp) as usize] = mmc3_chrprg[(2 + i) as usize];
                                    }
                                    tmp = mmc3_bits >> 5 & 2;
                                    prg[(0 + tmp) as usize] = mmc3_chrprg[6];
                                    prg[1] = mmc3_chrprg[7];
                                    prg[3] = rombuf[4] * 2 - 1;
                                    prg[(2 - tmp) as usize] = prg[3] - 1;
                                }
                                5 => { // Mirroring
                                    if addr1 == 0 {
                                        mirror = 2 + _val % 2;
                                    }
                                }
                                6 => { // IRQ Latch
                                    if addr1 == 0 {
                                        mmc3_latch = _val;
                                    }
                                }
                                7 => { // IRQ Enable
                                    mmc3_irq = addr1;
                                }
                                _ => {}
                            }
                        }
                        3 => { // mapper 3
                            chr[0] = _val % 4 * 2;
                            chr[1] = chr[0] + 1;
                        }
                        2 => { // mapper 2
                            prg[0] = _val & 31;
                        }
                        1 => { // mapper 1
                            if _val & 0x80 != 0 {
                                mmc1_bits = 5;
                                mmc1_data = 0;
                                mmc1_ctrl |= 12;
                            }
                            else {
                                mmc1_data = mmc1_data / 2 | _val << 4 & 16;
                                mmc1_bits -= 1;
                                if mmc1_bits == 0 {
                                    tmp = (addr >> 13) as u8;
                                    match tmp {
                                        4 => {
                                            mirror = mmc1_data & 3;
                                            mmc1_ctrl = mmc1_data;
                                        }
                                        5 => chrbank0 = mmc1_data,
                                        6 => chrbank1 = mmc1_data,
                                        _ => prgbank = mmc1_data,
                                    }

                                    // Update CHR banks.
                                    chr[0] = chrbank0 & if mmc1_ctrl & 16 != 0 { !0 } else { !1 };
                                    chr[1] = if mmc1_ctrl & 16 != 0 {
                                        chrbank1
                                    }
                                    else {
                                        chrbank0 | 1
                                    };

                                    // Update PRG banks.
                                    tmp = mmc1_ctrl / 4 % 4 - 2;
                                    prg[0] = if tmp == 0 {
                                        0
                                    } else if tmp == 1 {
                                        prgbank
                                    } 
                                    else { 
                                        prgbank & !1
                                    };
                                    prg[1] = if tmp == 0 {
                                        prgbank
                                    } else if tmp == 1 {
                                        rombuf[4] - 1
                                    } else {
                                        prgbank | 1
                                    };
                                }
                            }
                        }
                        _ => {}
                    }
                }
                return *rom.add(
                        (
                            ((prg[((hi - 8) >> (prgbits - 12)) as usize] as usize
                            & (((rombuf[4] as usize) << (14 - prgbits)) - 1))
                            << prgbits)
                            | ((addr as usize) & ((1 << prgbits) - 1))
                        ) as usize
                    )
            } 
        }

    return !0;
    }
}

// Read a byte at address `PCH:PCL` and increment PC.
fn read_pc() -> u8 {
    unsafe {
        val = mem(PCL, PCH, 0, 0);
        PCL = PCL.wrapping_add(1);
        if PCL == 0 {
            PCH = PCH.wrapping_add(1);
        }
        return val;
    }
}

// Set N (negative) and Z (zero) flags of `P` register, based on `val`.
fn set_nz(_val: u8) -> u8 {
    unsafe {
        P = P & 125 | _val & 128 | (_val == 0) as u8 * 2;
        P
    }
}

fn goto_nmi_irq() {
    unsafe {
        push(PCH);
        push(PCL);
        push(P | 32);
        // BRK/IRQ vector is $ffff, NMI vector is $fffa
        let veclo: u8 = !1 - (nmi_irq & 4);
        PCL = mem(veclo, !0, 0, 0);
        PCH = mem(veclo + 1, !0, 0, 0);
        nmi_irq = 0;
        cycles += 1;
    }
}

fn goto_nomemop() {
    unsafe {
        result = 0;
        match opcode & 227 {
            1 => { // ORA
                A |= val;
                set_nz(A);
            }
            33 => {  // AND
                A &= val;
                set_nz(A);
            }
            65 => { // EOR
                A ^= val;
                set_nz(A);
            }
            225 => { // SBC
                val = !val;
                // fallthrough
                sum = (A as u16) + (val as u16) + ((P % 2) as u16);
                P = P & !65 | (sum > 255) as u8 | ((A ^ sum as u8) & (val ^ sum as u8) & 128) / 2;
                A = sum as u8;
                set_nz(A);
            }
            97 => { // ADC
                sum = (A as u16) + (val as u16) + ((P % 2) as u16);
                P = P & !65 | (sum > 255) as u8 | ((A ^ sum as u8) & (val ^ sum as u8) & 128) / 2;
                A = sum as u8;
                set_nz(A);
            }
            34 => { // ROL
                result = P & 1;
                // fallthrough
                result |= val.wrapping_mul(2);
                P = P & !1 | val / 128;
                goto_memop();
            }
            2 => { // ASL
                result |= val.wrapping_mul(2);
                P = P & !1 | val / 128;
                goto_memop();
            }

            98 => { // ROR
                result = P << 7;
                // fallthrough
                result |= val / 2;
                P = P & !1 | val & 1;
                goto_memop();
            }
            66 => { // LSR
                result |= val / 2;
                P = P & !1 | val & 1;
                goto_memop();
            }

            194 => { // DEC
                result = val.wrapping_sub(1);
                goto_memop();
            }

            226 => { // INC
                result = val.wrapping_add(1);
                // fallthrough
                goto_memop();
            }

            32 => { // BIT
                P = P & 61 | val & 192 | ((A & val) == 0) as u8 * 2;
            }

            64 => { // JMP
                PCL = addr_lo;
                PCH = addr_hi;
                cycles -= 1;
            }

            96 => { // JMP indirect
                PCL = val;
                PCH = mem(addr_lo.wrapping_add(1), addr_hi, 0, 0);
                cycles += 1;
            }

            _ => {
                let opcodehi3: u8 = opcode / 32;
                let reg: *mut u8 = if opcode % 4 == 2 || opcodehi3 == 7 {
                    &mut X as *mut u8
                } else if opcode % 4 == 1 {
                    &mut A as *mut u8
                } else {
                    &mut Y as *mut u8
                };
                if opcodehi3 == 4 {  // STY/STA/STX
                    mem(addr_lo, addr_hi, *reg, 1);
                } else if opcodehi3 != 5 {  // CPY/CMP/CPX
                    P = P & !1 | (*reg >= val) as u8;
                    set_nz((*reg).wrapping_sub(val));
                } else {  // LDY/LDA/LDX
                    *reg = val;
                    set_nz(*reg);
                }
            }
        }
    }
}

fn goto_memop() {
    unsafe {
        set_nz(result);
        // Write result to A or back to memory.
        if nomem != 0 {
            A = result;
        } 
        else {
            (cycles += 2, mem(addr_lo, addr_hi, result, 1));
        } 
    }
}

fn goto_opcode() {
    unsafe {
        cycles = cycles.wrapping_add(2);
        if ((opcode != 76) as u8 & ((opcode & 224) != 128) as u8) != 0 {
            val = mem(addr_lo, addr_hi, 0, 0);
        }
    }
}

fn goto_add_x_or_y(opcodelo5: u8) {
    unsafe {
        val = if (opcodelo5 < 28) | (opcode == 190) {
            Y
        } else {
            X
        };
        cross = (addr_lo as u16 + val as u16 > 255) as u8;
        addr_hi = addr_hi.wrapping_add(cross);
        addr_lo = addr_lo.wrapping_add(val);
        cycles += ((((opcode & 224) == 128) | ((opcode % 16 == 14) & (opcode != 190))) as u8 | cross) as u16;
    }
}

fn main() {
    unsafe {
        let args: Vec<String> = env::args().collect();
        if args.len() < 2 {
            panic!("Usage: cargo run <rom.nes>");
        }

        // Convert Rust string to C string
        let c_filename = std::ffi::CString::new(args[1].as_str()).unwrap();
        let rw = SDL_RWFromFile(c_filename.as_ptr(), std::ffi::CString::new("rb").unwrap().as_ptr());
        if rw.is_null() {
            use sdl2_sys::SDL_GetError;
            let err = SDL_GetError();
            panic!(
                "SDL_RWFromFile failed: {}",
                std::ffi::CStr::from_ptr(err).to_string_lossy()
            );
        }
        SDL_RWread(rw, rombuf.as_mut_ptr() as *mut c_void, 1024 * 1024, 1);
        
        // Start PRG0 after 16-byte header.
        rom = rombuf.as_ptr().wrapping_add(16);
        // PRG1 is the last bank. `rombuf[4]` is the number of 16k PRG banks.
        prg[1] = rombuf[4] - 1;
        // CHR0 ROM is after all PRG data in the file. `rombuf[5]` is the number of
        // 8k CHR banks. If it is zero, assume the game uses CHR RAM.
        chrrom = if rombuf[5] != 0 {
            rom.add((prg[1] as usize + 1) << 14) as *mut u8
        } 
        else {
            chrram.as_mut_ptr()
        };
        // CHR1 is the last 4k bank.
        chr[1] = 1;
        // Bit 0 of `rombuf[6]` is 0=>horizontal mirroring, 1=>vertical mirroring.
        mirror = 3 - rombuf[6] % 2;
        if rombuf[6] / 16 == 4 {
            mem(0, 128, 0, 1); // Update to default mmc3 banks
            prgbits -= 1;         // 8kb PRG banks
            chrbits -= 2;      // 1kb CHR banks
        }

        // Start at address in reset vector, at $FFFC.
        PCL = mem(!3, !0, 0, 0);
        PCH = mem(!2, !0, 0, 0);

        sdl2_sys::SDL_Init(SDL_INIT_VIDEO);

        key_state = sdl2_sys::SDL_GetKeyboardState(std::ptr::null_mut()) as *mut u8;
        // Create window 1024x840. The framebuffer is 256x240, but we don't draw the
        // top or bottom 8 rows. Scaling up by 4x gives 1024x960, but that looks
        // squished because the NES doesn't have square pixels. So shrink it by 7/8.
        let renderer = SDL_CreateRenderer(
            SDL_CreateWindow("smolnes".as_ptr() as *const i8, 0, 0, 1024, 840, SDL_WINDOW_SHOWN as u32), -1,
            SDL_RENDERER_PRESENTVSYNC as u32);
        let texture = SDL_CreateTexture(renderer, SDL_PIXELFORMAT_BGR565 as u32,
                                            SDL_TEXTUREACCESS_STREAMING as i32, 256, 224);

        loop {
            nomem = 0;
            cycles = 0;
            if nmi_irq != 0 {
                goto_nmi_irq();
                cycles += 4;
            }
            else {
                opcode = read_pc();
                let opcodelo5: u8 = opcode & 31;
                match opcodelo5 {
                    0 => {
                        if opcode & 0x80 != 0 { // LDY/CPY/CPX imm
                            read_pc();
                            nomem = 1;
                            goto_nomemop();
                        }
                        else {
                            match opcode >> 5 {
                                0 => { // BRK or nmi_irq
                                    PCL = PCL.wrapping_add(1);
                                    if PCL == 0 {
                                        PCH += 1;
                                    }
                                    goto_nmi_irq();
                                }

                                1 => { // JSR
                                    result = read_pc();
                                    push(PCH);
                                    push(PCL);
                                    PCH = read_pc();
                                    PCL = result;
                                } 

                                2 => { // RTI
                                    P = pull() & !32;
                                    PCL = pull();
                                    PCH = pull();
                                }

                                3 => { // RTS
                                    PCL = pull();
                                    PCH = pull();
                                    PCL = PCL.wrapping_add(1);
                                    if PCL == 0 {
                                        PCH += 1;
                                    }
                                }

                                _ => {}
                            }

                            cycles += 4;
                        }
                    }

                    16 => { // BPL, BMI, BVC, BVS, BCC, BCS, BNE, BEQ
                        read_pc();
                        if ((P & mask[(opcode >> 6) as usize]) != 0) as u8 ^ (opcode / 32 & 1) == 0 {
                            cross = ((PCL as i16 + val as i8 as i16) >> 8) as u8;
                            PCH = PCH.wrapping_add(cross);
                            PCL = PCL.wrapping_add(val);
                            cycles += if cross != 0 { 2 } else { 1 };
                        }
                    }

                    8 | 24 => {
                        opcode >>= 4;
                        match opcode {
                            0 => { // PHP
                                push(P | 48);
                                cycles += 1;
                            }

                            2 => { // PLP
                                P = pull() & !16;
                                cycles += 2;
                            }

                            4 => { // PHA
                                push(A);
                                cycles += 1;
                            }
                            
                            6 => { // PLA
                                A = pull();
                                set_nz(A);
                                cycles += 2;
                            }

                            8 => { // DEY
                                Y = Y.wrapping_sub(1);
                                set_nz(Y);
                            }

                            9 => { // TYA
                                A = Y;
                                set_nz(A);
                            }

                            10 => { // TAY
                                Y = A;
                                set_nz(Y);
                            }

                            12 => { // INY
                                Y = Y.wrapping_add(1);
                                set_nz(Y);
                            }

                            14 => { // INX
                                X = X.wrapping_add(1);
                                set_nz(X);
                            }

                            _ => { // CLC, SEC, CLI, SEI, CLV, CLD, SED
                                P = P & !mask[(opcode + 3) as usize] | mask[(opcode + 4) as usize];
                            }
                        }
                    }
                
                    10 | 26 => {
                        match opcode >> 4 {
                            8 => { // TXA
                                A = X;
                                set_nz(A);
                            }

                            9 => { // TXS
                                S = X;
                            }

                            10 => { // TAX
                                X = A;
                                set_nz(X);
                            }

                            11 => { // TSX
                                X = S;
                                set_nz(X);
                            }

                            12 => { // DEX
                                X = X.wrapping_sub(1);
                                set_nz(X);
                            }

                            14 => { } // NOP
                            
                            _ => { // ASL/ROL/LSR/ROR A
                                nomem = 1;
                                val = A;
                                goto_nomemop();
                            }
                        }
                    }


                    1 => { // X-indexed, indirect
                        read_pc();
                        val = val.wrapping_add(X);
                        addr_lo = mem(val, 0, 0, 0);
                        addr_hi = mem(val.wrapping_add(1), 0, 0, 0);
                        cycles += 4;
                        goto_opcode();
                        goto_nomemop();
                    }

                    2 | 9 => { // Immediate
                        read_pc();
                        nomem = 1;
                        goto_nomemop();
                    }

                    17 => { // Zeropage, Y-indexed
                        addr_lo = mem(read_pc(), 0, 0, 0);
                        addr_hi = mem(val.wrapping_add(1), 0, 0, 0);
                        cycles += 1;
                        goto_add_x_or_y(opcodelo5);
                        goto_opcode();
                        goto_nomemop();
                    }

                    4 | 5 | 6 |       // Zeropage +1
                    20 | 21 | 22 => { // Zeropage, X-indexed +2
                        addr_lo = read_pc();
                        cross = (opcodelo5 > 6) as u8;
                        if cross != 0 {
                            addr_lo = addr_lo.wrapping_add(if (opcode & 214) == 150  {  // LDX/STX use Y
                                Y
                            } else {
                                X
                            });
                        }
                        addr_hi = 0;
                        cycles = cycles.wrapping_sub((cross == 0) as u16);
                        goto_opcode();
                        goto_nomemop();
                    }

                    12 | 13 | 14 |    // Absolute               +2
                    25 |              // Absolute, Y-indexed    +2/3
                    28 | 29 | 30 => { // Absolute, X-indexed    +2/3
                        addr_lo = read_pc();
                        addr_hi = read_pc();
                        if opcodelo5 >= 25 {
                            goto_add_x_or_y(opcodelo5);
                        };
                        goto_opcode();
                        goto_nomemop();
                    }

                    _ => {}
                }
            }

            // Update PPU, which runs 3 times faster than CPU. Each CPU instruction
            // takes at least 2 cycles.
            let mut _tmp = cycles * 3 + 6;
            while _tmp > 0 {
                _tmp -= 1;
                if ppumask & 24 != 0 { // If background or sprites are enabled.
                    if scany < 240 {
                        if dot < 256 || dot >= 320 {  // dot [0..255,320..340]
                            // Draw a pixel to the framebuffer.
                            if dot < 256 {
                                // Read color and palette from shift registers.
                                let mut color: u8 = (((shift_hi >> (14 - fine_x)) & 2) | ((shift_lo >> (15 - fine_x)) & 1)) as u8;
                                let mut palette: u8 = ((shift_at >> (28 - fine_x * 2)) & 12) as u8;

                                // If sprites are enabled.
                                if ppumask & 16 != 0 {
                                    // Loop through all sprites.
                                    for sprite in oam.chunks(4) {
                                        let sprite_h: u16 = if ppuctrl & 32 != 0 {
                                            16
                                        }
                                        else {
                                            8
                                        };
                                        let sprite_x: u16 = dot.wrapping_sub(sprite[3] as u16);
                                        let sprite_y: u16 = scany.wrapping_sub(sprite[0] as u16).wrapping_sub(1);
                                        let sx: u16 = sprite_x ^ ((sprite[2] & 64) == 0) as u16 * 7;
                                        let sy: u16 = sprite_y ^ (if sprite[2] & 128 != 0 { sprite_h - 1 } else { 0 });
                                    
                                        if sprite_x < 8 && sprite_y < sprite_h {
                                            let sprite_tile: u16 = sprite[1] as u16;
                                            let sprite_addr: u16 = if ppuctrl & 32 != 0 {
                                                // 8x16 sprites
                                                sprite_tile % 2 << 12 | sprite_tile << 4 & !32 | sy * 2 & 16
                                            }
                                            else {
                                                // 8x8 sprites
                                                (ppuctrl as u16 & 8) << 9 | sprite_tile << 4 | sy & 7
                                            };
                                            let sprite_color: u16 = (*get_chr_byte(sprite_addr + 8) >> sx << 1 & 2 | *get_chr_byte(sprite_addr) >> sx & 1) as u16;

                                            // Only draw sprite if color is not 0 (transparent)
                                            if sprite_color != 0 {
                                                // Don't draw sprite if BG has priority.
                                                if !(sprite[2] & 32 != 0 && color != 0) {
                                                    color = sprite_color as u8;
                                                    palette = 16 | sprite[2].wrapping_mul(4) & 12;
                                                }
                                                // Maybe set sprite0 hit flag.
                                                if sprite.as_ptr() == oam.as_ptr() && color != 0 {
                                                    ppustatus |= 64;
                                                }
                                                break;
                                            }
                                        }
                                    }
                                }

                                // Write pixel to framebuffer. Always use palette 0 for color 0.
                                // BGR565 palette is used instead of RGBA32 to reduce source code
                                // size.
                                frame_buffer[(scany * 256 + dot) as usize] =
                                    [
                                        25356, 34816, 39011, 30854, 24714, 4107,  106,   2311,
                                        2468,  2561,  4642,  6592,  20832, 0,     0,     0,
                                        44373, 49761, 55593, 51341, 43186, 18675, 434,   654,
                                        4939,  5058,  3074,  19362, 37667, 0,     0,     0,
                                        !0u16,    !819u16,  64497, 64342, 62331, 43932, 23612, 9465,
                                        1429,  1550,  20075, 36358, 52713, 16904, 0,     0,
                                        !0u16,    !328u16, !422u16, !452u16, !482u16, 58911, 50814, 42620,
                                        40667, 40729, 48951, 53078, 61238, 44405
                                    ]
                                    [palette_ram[(if color != 0 { palette  | color } else { 0 }) as usize] as usize];
                            }

                            // Update shift registers every cycle.
                            if dot < 336 {
                                shift_hi = shift_hi.wrapping_mul(2);
                                shift_lo = shift_lo.wrapping_mul(2);
                                shift_at = shift_at.wrapping_mul(4);
                            }

                            let _temp = (ppuctrl as u16) << 8 & 4096 | (ntb as u16) << 4 | V >> 12;
                            match dot & 7 {
                                1 => { // Read nametable byte.
                                    ntb = *get_nametable_byte(V);
                                }
                                3 => { // Read attribute byte.
                                    atb = ((*get_nametable_byte(V & 0xc00 | 0x3c0 | V >> 4 & 0x38 |
                                                            V / 4 & 7) >>
                                        (V >> 5 & 2 | V / 2 & 1) * 2) as u16 %
                                        4 * 0x5555) as u16;
                                }
                                5 => { // Read pattern table low byte.
                                    ptb_lo = *get_chr_byte(_temp as u16);
                                }
                                7 => { // Read pattern table high byte.
                                    let ptb_hi: u8 = *get_chr_byte(_temp as u16 | 8);
                                    // Increment horizontal VRAM read address.
                                    V = if V % 32 == 31 {
                                        V & !31 ^ 1024
                                    }
                                    else {
                                        V + 1
                                    };
                                    shift_hi |= ptb_hi as u16;
                                    shift_lo |= ptb_lo as u16;
                                    shift_at |= atb as u32;
                                }
                                _ => {}
                            }
                        }
                    }

                    // Increment vertical VRAM address.
                    if dot == 256 {
                        V = (if (V & (7 << 12)) != (7 << 12) {
                            V + 4096
                        } else if (V & 0x3e0) == 928 {
                            (V & 0x8c1f) ^ 2048
                        } else if (V & 0x3e0) == 0x3e0 {
                            V & 0x8c1f
                        } else {
                            (V & 0x8c1f) | ((V + 32) & 0x3e0)
                        }) & !0x41f | (T & 0x41f);
                    }

                    // Check for MMC3 IRQ.
                    if (scany + 1) % 262 < 241 && dot == 261 && mmc3_irq != 0 {
                        if mmc3_latch == 0 {
                            nmi_irq = 1;
                        }
                        mmc3_latch = mmc3_latch.wrapping_sub(1);
                    }
        
                    // Reset vertical VRAM address to T value.
                    if scany == 261 && dot.wrapping_sub(280) < 25u16 {  // dot [280..304]
                        V = V & 0x841f | T & 0x7be0;
                    }
                }


                if dot == 1 {
                    if scany == 241 {
                        // If NMI is enabled, trigger NMI.
                        if ppuctrl & 128 != 0 {
                            nmi_irq = 4;
                        }
                        ppustatus |= 128;
                        // Render frame, skipping the top and bottom 8 pixels (they're often
                        // garbage).
                        SDL_UpdateTexture(texture, std::ptr::null(), frame_buffer.as_ptr().add(2048) as *const c_void, 512);
                        SDL_RenderCopy(renderer, texture, std::ptr::null(), std::ptr::null());
                        SDL_RenderPresent(renderer);
                        // Handle SDL events.
                        let mut event: SDL_Event = std::mem::zeroed();
                        while SDL_PollEvent(&mut event) != 0 {
                            if event.type_ == SDL_QUIT as u32 {
                                return;
                            }
                        }
                    }

                    // Clear ppustatus.
                    if scany == 261 {
                        ppustatus = 0;
                    }
                }

                // Increment to next dot/scany. 341 dots per scanline, 262 scanlines per
                // frame. Scanline 261 is represented as -1.
                dot += 1;
                if dot == 341 {
                    dot = 0;
                    scany += 1;
                    scany %= 262;
                }
            }
        }
    }
}

