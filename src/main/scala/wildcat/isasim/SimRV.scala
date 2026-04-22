/*
 * Copyright (c) 2015-2017, DTU
 * Simplified BSD License
 */

/*
 * A simple ISA simulator of RISC-V.
 *
 * Author: Martin Schoeberl (martin@jopdesign.com)
 *
 * Extended for Linux boot:
 *   - RAM relocated to MEM_BASE (0x80000000)
 *   - Minimal CLINT at 0x02000000 (mtime, mtimecmp, msip)
 *   - Minimal PLIC at 0x0c000000 (swallows accesses, returns 0)
 *   - 8250 UART at 0x10000000 (byte-wise)
 *   - SYSTEM opcode properly decoded (ecall/ebreak/mret/sret/wfi/sfence.vma)
 *   - Top-level exception catch with diagnostic
 */

package wildcat.isasim

import net.fornwall.jelf.ElfFile

import wildcat.Opcode._
import wildcat.AluFunct3._
import wildcat.AluFunct7._
import wildcat.BranchFunct3._
import wildcat.LoadStoreFunct3._
import wildcat.CSRFunct3._
import wildcat.InstrType._
import wildcat.CSR._
import wildcat.Util

class SimRV(mem: Array[Int], start: Int, stop: Int) {
  import SimRV._

  // Processor state
  var pc = start
  var reg = new Array[Int](32)
  reg(0) = 0

  // LR/SC reservation
  var reservationValid = false
  var reservationAddr = 0

  // CLINT timer state
  private var instCount: Long = 0L
  private var mtimecmp: Long = Long.MaxValue // no pending timer by default

  // halt flag
  var run = true

  // Translate a physical address into an index into `mem` (word array).
  // Throws if the address is outside RAM.
  @inline private def memIdx(addr: Int): Int = {
    // (addr - MEM_BASE) is computed in 2's-complement Int and is correct
    // as an unsigned offset; >>> 2 gives the word index.
    val idx = (addr - MEM_BASE) >>> 2
    if (idx < 0 || idx >= mem.length) {
      throw new RuntimeException(
        f"RAM access out of bounds: addr=0x$addr%08x (idx=$idx, mem.length=${mem.length})"
      )
    }
    idx
  }

  // MMIO region predicates
  @inline private def isUart(addr: Int): Boolean =
    addr >= 0x10000000 && addr < 0x10000100
  @inline private def isClint(addr: Int): Boolean =
    addr >= 0x02000000 && addr < 0x02010000
  @inline private def isPlic(addr: Int): Boolean =
    addr >= 0x0c000000 && addr < 0x10000000

  // CLINT load
  private def clintLoad(addr: Int): Int = {
    val off = addr - 0x02000000
    off match {
      case 0xbff8 => (instCount & 0xffffffffL).toInt // mtime lo
      case 0xbffc => ((instCount >>> 32) & 0xffffffffL).toInt // mtime hi
      case 0x4000 => (mtimecmp & 0xffffffffL).toInt // mtimecmp lo
      case 0x4004 => ((mtimecmp >>> 32) & 0xffffffffL).toInt // mtimecmp hi
      case 0x0000 => 0 // msip (hart 0)
      case _      => 0
    }
  }

  // CLINT store
  private def clintStore(addr: Int, value: Int): Unit = {
    val off = addr - 0x02000000
    off match {
      case 0x4000 =>
        mtimecmp =
          (mtimecmp & 0xffffffff00000000L) | (value.toLong & 0xffffffffL)
      case 0x4004 =>
        mtimecmp =
          (mtimecmp & 0x00000000ffffffffL) | ((value.toLong & 0xffffffffL) << 32)
      case _ => () // msip + everything else: ignore
    }
  }

  private val csrs = scala.collection.mutable.HashMap[Int, Int](
    0x300 -> 0x00001800, // mstatus: MPP = M-mode, MIE = 0
    0x301 -> 0x40001100, // misa:    RV32IMA
    0x304 -> 0, // mie
    0x305 -> 0, // mtvec
    0x340 -> 0, // mscratch
    0x341 -> 0, // mepc
    0x342 -> 0, // mcause
    0x343 -> 0, // mtval
    0x344 -> 0, // mip
    0xf11 -> 0, // mvendorid
    0xf12 -> WILDCAT_MARCHID, // marchid
    0xf13 -> 0, // mimpid
    0xf14 -> 0 // mhartid
  )
  private val readOnlyCsrs = Set(0x301, 0xf11, 0xf12, 0xf13, 0xf14)

  private def csrRead(addr: Int): Int = csrs.getOrElse(addr, 0)
  private def csrWrite(addr: Int, value: Int): Unit =
    if (!readOnlyCsrs.contains(addr)) csrs(addr) = value

  def execute(instr: Int): Boolean = {
    val opcode = instr & 0x7f
    val rd = (instr >> 7) & 0x01f
    val rs1 = (instr >> 15) & 0x01f
    val rs2 = (instr >> 20) & 0x01f
    val funct3 = (instr >> 12) & 0x07
    val funct7 = (instr >> 25) & 0x07f

    def genImm() = {
      val instrType: InstrType = opcode match {
        case AluImm => I
        case Alu    => R
        case Branch => SBT
        case Load   => I
        case Store  => S
        case Lui    => U
        case AuiPc  => U
        case Jal    => UJ
        case JalR   => I
        case System => I
        case _      => R
      }
      val instr7 = (instr >> 7) & 0x01
      val instr11_8 = (instr >> 8) & 0x0f
      val instr19_12 = (instr >> 12) & 0xff
      val instr20 = (instr >> 20) & 0x01
      val instr24_21 = (instr >> 21) & 0x0f
      val instr31_20 = (instr >> 20) & 0xfff
      val instr30_25 = (instr >> 25) & 0x3f
      val instr31 = (instr >> 31) & 0x01
      val sext8 = if (instr31 == 1) 0xff else 0
      val sext12 = if (instr31 == 1) 0xfff else 0

      val imm0 = instrType match {
        case I => instr20
        case S => instr7
        case _ => 0
      }
      val imm4_1 = instrType match {
        case I  => instr24_21
        case U  => 0
        case UJ => instr24_21
        case _  => instr11_8
      }
      val imm10_5 = if (instrType == U) 0 else instr30_25
      val imm11 = instrType match {
        case SBT => instr7
        case U   => 0
        case UJ  => instr20
        case _   => instr31
      }
      val imm19_12 =
        if (instrType == U || instrType == UJ) instr19_12 else sext8
      val imm31_20 = if (instrType == U) instr31_20 else sext12

      (imm31_20 << 20) | (imm19_12 << 12) | (imm11 << 11) |
        (imm10_5 << 5) | (imm4_1 << 1) | imm0
    }

    val imm = genImm()

    val sraSub =
      funct7 == SRA_SUB && (opcode == Alu || (opcode == AluImm && funct3 == F3_SRL_SRA))

    def alu(funct3: Int, sraSub: Boolean, op1: Int, op2: Int): Int = {
      val shamt = op2 & 0x1f
      funct3 match {
        case F3_ADD_SUB => if (sraSub) op1 - op2 else op1 + op2
        case F3_SLL     => op1 << shamt
        case F3_SLT     => if (op1 < op2) 1 else 0
        case F3_SLTU    => if ((op1 < op2) ^ (op1 < 0) ^ (op2 < 0)) 1 else 0
        case F3_XOR     => op1 ^ op2
        case F3_SRL_SRA => if (sraSub) op1 >> shamt else op1 >>> shamt
        case F3_OR      => op1 | op2
        case F3_AND     => op1 & op2
      }
    }

    def mulDiv(funct3: Int, op1: Int, op2: Int): Int = {
      val a = op1.toLong
      val b = op2.toLong
      val au = op1.toLong & 0xffffffffL
      val bu = op2.toLong & 0xffffffffL
      funct3 match {
        case F3_MUL    => ((a * b) & 0xffffffffL).toInt
        case F3_MULH   => ((a * b) >> 32).toInt
        case F3_MULHSU => ((a * bu) >> 32).toInt
        case F3_MULHU  => ((au * bu) >> 32).toInt
        case F3_DIV    => if (b == 0) -1 else (a / b).toInt
        case F3_DIVU   => if (bu == 0) -1 else (au / bu).toInt
        case F3_REM    => if (b == 0) a.toInt else (a % b).toInt
        case F3_REMU   => if (bu == 0) au.toInt else (au % bu).toInt
      }
    }

    def compare(funct3: Int, op1: Int, op2: Int): Boolean = funct3 match {
      case BEQ  => op1 == op2
      case BNE  => !(op1 == op2)
      case BLT  => op1 < op2
      case BGE  => op1 >= op2
      case BLTU => (op1 < op2) ^ (op1 < 0) ^ (op2 < 0)
      case BGEU => op1 == op2 || ((op1 > op2) ^ (op1 < 0) ^ (op2 < 0))
    }

    def load(funct3: Int, base: Int, displ: Int): Int = {
      val addr = base + displ

      // MMIO: UART (byte registers; reg-io-width=1, reg-shift=0)
      if (isUart(addr)) {
        val offset = addr - 0x10000000
        return offset match {
          case 5 => 0x60 // LSR: THRE | TEMT  (transmit always ready)
          case _ => 0x00
        }
      }

      // MMIO: CLINT
      if (isClint(addr)) return clintLoad(addr)

      // MMIO: PLIC — reads return 0, that's enough for boot
      if (isPlic(addr)) return 0

      // RAM
      val data = mem(memIdx(addr))
      funct3 match {
        case LB  => (((data >> (8 * (addr & 0x03))) & 0xff) << 24) >> 24
        case LH  => (((data >> (8 * (addr & 0x03))) & 0xffff) << 16) >> 16
        case LW  => data
        case LBU => (data >> (8 * (addr & 0x03))) & 0xff
        case LHU => (data >> (8 * (addr & 0x03))) & 0xffff
      }
    }

    def store(funct3: Int, base: Int, displ: Int, value: Int): Unit = {
      val addr = base + displ

      // MMIO: UART
      if (isUart(addr)) {
        val offset = addr - 0x10000000
        funct3 match {
          case SB if offset == 0 =>
            print((value & 0xff).toChar)
            Console.out.flush()
          case _ =>
          // writes to IER/FCR/LCR/MCR/SCR — no-op
        }
        return
      }

      // MMIO: CLINT
      if (isClint(addr)) { clintStore(addr, value); return }

      // MMIO: PLIC
      if (isPlic(addr)) return

      // RAM
      val wordAddr = memIdx(addr)

      if (
        reservationValid && wordAddr == (reservationAddr >>> 2) - (MEM_BASE >>> 2)
      ) {
        // Conservative: any store in RAM invalidates a matching reservation.
        reservationValid = false
      }

      funct3 match {
        case SB =>
          val mask = (addr & 0x03) match {
            case 0 => 0xffffff00
            case 1 => 0xffff00ff
            case 2 => 0xff00ffff
            case 3 => 0x00ffffff
          }
          mem(wordAddr) =
            (mem(wordAddr) & mask) | ((value & 0xff) << (8 * (addr & 0x03)))
        case SH =>
          val mask = (addr & 0x03) match {
            case 0 => 0xffff0000
            case 2 => 0x0000ffff
            case o =>
              throw new RuntimeException(
                f"Misaligned SH at 0x$addr%08x (off=$o)"
              )
          }
          mem(wordAddr) =
            (mem(wordAddr) & mask) | ((value & 0xffff) << (8 * (addr & 0x03)))
        case SW =>
          mem(wordAddr) = value
      }
    }

    // SYSTEM opcode: separate priv instructions (funct3=0) from CSR ops (funct3!=0)
    def systemOp(): (Int, Boolean, Int) = {
      val pcNext = pc + 4
      if (funct3 == 0) {
        val f7 = (instr >>> 25) & 0x7f
        val imm12 = (instr >>> 20) & 0xfff
        if (f7 == 0x09 || f7 == 0x0b) {
          // sfence.vma / sinval.vma: no-op (no MMU)
          (0, false, pcNext)
        } else
          imm12 match {
            case 0x000 =>
              // ECALL. Linux nommu without SBI shouldn't execute these.
              // Log and continue instead of halting.
              Console.err.println(
                f"WARN: ecall at pc=0x$pc%08x (a7=0x${reg(17)}%08x)"
              )
              (0, false, pcNext)
            case 0x001 => // EBREAK  — real trap into mtvec if set
              val tvec = csrRead(0x305)
              if ((tvec & ~0x3) != 0) {
                csrWrite(0x341, pc) // mepc  = offending pc
                csrWrite(0x342, 3) // mcause = breakpoint
                val s = csrRead(0x300)
                val mie = (s >>> 3) & 1
                csrWrite(0x300, (s & ~0x88) | (mie << 7)) // MPIE = MIE; MIE = 0
                (0, false, tvec & ~0x3)
              } else {
                Console.err.println(
                  f"EBREAK at pc=0x$pc%08x (no mtvec installed)"
                )
                run = false
                (0, false, pcNext)
              }
            case 0x102 | 0x302 => // SRET / MRET — return from trap
              val epc = csrRead(0x341) // use mepc (nommu = M-mode)
              val s = csrRead(0x300)
              val mpie = (s >>> 7) & 1
              csrWrite(
                0x300,
                (s & ~0x8) | (mpie << 3) | 0x80
              ) // MIE = MPIE; MPIE = 1
              (0, false, epc)
            case 0x105 =>
              // WFI — no-op (we don't deliver interrupts anyway)
              (0, false, pcNext)
            case _ =>
              Console.err.println(
                f"Unknown SYSTEM f3=0 imm12=0x$imm12%03x at pc=0x$pc%08x — treating as nop"
              )
              (0, false, pcNext)
          }
      } else {
        // CSR read/write — return 0 / MARCHID, silently accept writes
        (csrOp(), true, pcNext)
      }
    }

    def csrOp(): Int = {
      val csr = imm & 0xfff
      val old = csrRead(csr)
      val src = funct3 match {
        case CSRRW | CSRRS | CSRRC    => reg(rs1)
        case CSRRWI | CSRRSI | CSRRCI => rs1 // 5-bit zimm lives in rs1 slot
        case _                        => 0
      }
      // For Set/Clear, skip the write if source is x0/zimm0 (spec requirement)
      val doWrite = funct3 match {
        case CSRRW | CSRRWI                  => true
        case CSRRS | CSRRSI | CSRRC | CSRRCI => rs1 != 0
        case _                               => false
      }
      if (doWrite) {
        val nw = funct3 match {
          case CSRRW | CSRRWI => src
          case CSRRS | CSRRSI => old | src
          case CSRRC | CSRRCI => old & ~src
        }
        csrWrite(csr, nw)
      }
      old
    }

    def atomic(funct5: Int, addr: Int, rs2Val: Int): (Int, Boolean) = {
      if ((addr & 0x3) != 0) {
        throw new RuntimeException(f"Misaligned atomic address: 0x$addr%08x")
      }
      val wordAddr = memIdx(addr)
      val oldValue = mem(wordAddr)

      funct5 match {
        case 0x02 => // LR.W
          reservationValid = true
          reservationAddr = addr
          (oldValue, true)
        case 0x03 => // SC.W
          if (reservationValid && reservationAddr == addr) {
            mem(wordAddr) = rs2Val
            reservationValid = false
            (0, true)
          } else (1, true)
        case 0x01 => // AMOSWAP
          mem(wordAddr) = rs2Val; (oldValue, true)
        case 0x00 => // AMOADD
          mem(wordAddr) = oldValue + rs2Val; (oldValue, true)
        case 0x04 => // AMOXOR
          mem(wordAddr) = oldValue ^ rs2Val; (oldValue, true)
        case 0x0c => // AMOAND
          mem(wordAddr) = oldValue & rs2Val; (oldValue, true)
        case 0x08 => // AMOOR
          mem(wordAddr) = oldValue | rs2Val; (oldValue, true)
        case 0x10 => // AMOMIN
          mem(wordAddr) = math.min(oldValue, rs2Val); (oldValue, true)
        case 0x14 => // AMOMAX
          mem(wordAddr) = math.max(oldValue, rs2Val); (oldValue, true)
        case 0x18 => // AMOMINU
          val a = oldValue.toLong & 0xffffffffL
          val b = rs2Val.toLong & 0xffffffffL
          mem(wordAddr) = (if (a < b) a else b).toInt
          (oldValue, true)
        case 0x1c => // AMOMAXU
          val a = oldValue.toLong & 0xffffffffL
          val b = rs2Val.toLong & 0xffffffffL
          mem(wordAddr) = (if (a > b) a else b).toInt
          (oldValue, true)
        case _ =>
          Console.err.println(
            f"Unknown AMO funct5=0x$funct5%02x at pc=0x$pc%08x"
          )
          (0, false)
      }
    }

    val rs1Val = reg(rs1)
    val rs2Val = reg(rs2)
    val pcNext = pc + 4

    val result = opcode match {
      case 0x2f => // AMO
        val addr = rs1Val
        if (funct3 != 0x2) {
          throw new RuntimeException(
            f"Invalid funct3=0x$funct3%x for AMO at pc=0x$pc%08x"
          )
        }
        val funct5 = (funct7 >> 2) & 0x1f
        val (value, success) = atomic(funct5, addr, rs2Val)
        (value, success, pcNext)

      case AluImm => (alu(funct3, sraSub, rs1Val, imm), true, pcNext)
      case Alu if funct7 == 0x01 =>
        (mulDiv(funct3, rs1Val, rs2Val), true, pcNext)
      case Alu    => (alu(funct3, sraSub, rs1Val, rs2Val), true, pcNext)
      case Branch =>
        (0, false, if (compare(funct3, rs1Val, rs2Val)) pc + imm else pcNext)
      case Load   => (load(funct3, rs1Val, imm), true, pcNext)
      case Store  => store(funct3, rs1Val, imm, rs2Val); (0, false, pcNext)
      case Lui    => (imm, true, pcNext)
      case AuiPc  => (pc + imm, true, pcNext)
      case Jal    => (pc + 4, true, pc + imm)
      case JalR   => (pc + 4, true, (rs1Val + imm) & 0xfffffffe)
      case Fence  => (0, false, pcNext) // fence / fence.i: no-op
      case System => systemOp()
      case _      =>
        Console.err.println(
          f"Unknown opcode 0x$opcode%02x at pc=0x$pc%08x instr=0x$instr%08x — treating as nop"
        )
        (0, false, pcNext)
    }

    if (rd != 0 && result._2) reg(rd) = result._1

    val oldPc = pc
    pc = result._3

    // Keep running while:
    //  - execution flag is still set, AND
    //  - PC advanced (guards against a single-instruction self-loop)
    // Note: `pc < stop` using signed comparison is fine because both pc and stop
    // are in the same wrap-around region near 0x80000000.
    pc != oldPc && run && pc < stop
  }

  // -------------------------------------------------------------------------
  // Main execution loop with exception catching so problems are visible.
  // -------------------------------------------------------------------------
  var cont = true
  var steps: Long = 0L
  while (cont) {
    try {
      val instr = mem(memIdx(pc))
      cont = execute(instr)
      instCount += 1
      steps += 1
    } catch {
      case e: Throwable =>
        Console.err.println(
          f"\n*** SIM HALTED at pc=0x$pc%08x after $steps steps"
        )
        Console.err.println(
          s"***   reason: ${e.getClass.getSimpleName}: ${e.getMessage}"
        )
        Console.err.println("***   registers:")
        for (i <- 0 until 32) {
          Console.err.print(f"x$i%02d=0x${reg(i)}%08x ")
          if ((i & 3) == 3) Console.err.println()
        }
        cont = false
    }
  }
  Console.err.println(f"Simulation ended. pc=0x$pc%08x, steps=$steps")
}

object SimRV {

  // Physical base of RAM. Must match the kernel's CONFIG_PHYS_RAM_BASE and
  // the `. = 0x80000000;` in boot.ld and the memory@80000000 node in wildcat.dts.
  val MEM_BASE = 0x80000000

  val memSize = 8 // MB
  val memWords = memSize * 1024 * 1024 / 4
  val maxAddr = memSize * 1024 * 1024 - 1

  def runSimRV(file: String) = {
    val mem = new Array[Int](memWords)

    val (code, startOrig) = Util.getCode(file)

    for (i <- 0 until code.length) mem(i) = code(i)

    // boot.bin is a raw binary whose first byte is the bootloader entry
    // (`_start`), linked at MEM_BASE. For ELF inputs the entry comes from
    // the file itself; otherwise we default to MEM_BASE.
    val start =
      if (startOrig == 0 || startOrig == MEM_BASE) MEM_BASE
      else startOrig

    // Allow execution anywhere in RAM (the kernel branches all over 8 MB).
    val stop = MEM_BASE + memSize * 1024 * 1024

    new SimRV(mem, start, stop)
  }

  def main(args: Array[String]): Unit = {
    runSimRV(args(0))
  }
}
