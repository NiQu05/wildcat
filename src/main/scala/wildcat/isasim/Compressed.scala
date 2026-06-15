package wildcat

object Compressed {

  private def bits(value: Int, hi: Int, lo: Int): Int =
    (value >>> lo) & ((1 << (hi - lo + 1)) - 1)

  private def bit(value: Int, idx: Int): Int =
    (value >>> idx) & 1

  private def sext(value: Int, width: Int): Int = {
    val shift = 32 - width
    (value << shift) >> shift
  }

  private def rvcReg(value: Int): Int = 8 + value

  private def encodeR(funct7: Int, rs2: Int, rs1: Int, funct3: Int, rd: Int, opcode: Int): Int =
    (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode

  private def encodeI(imm: Int, rs1: Int, funct3: Int, rd: Int, opcode: Int): Int =
    ((imm & 0xfff) << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode

  private def encodeS(imm: Int, rs2: Int, rs1: Int, funct3: Int, opcode: Int): Int =
    (((imm >>> 5) & 0x7f) << 25) | (rs2 << 20) | (rs1 << 15) |
      (funct3 << 12) | ((imm & 0x1f) << 7) | opcode

  private def encodeB(imm: Int, rs2: Int, rs1: Int, funct3: Int, opcode: Int): Int =
    (((imm >>> 12) & 0x1) << 31) | (((imm >>> 5) & 0x3f) << 25) |
      (rs2 << 20) | (rs1 << 15) | (funct3 << 12) |
      (((imm >>> 1) & 0xf) << 8) | (((imm >>> 11) & 0x1) << 7) | opcode

  private def encodeU(imm: Int, rd: Int, opcode: Int): Int =
    (imm & 0xfffff000) | (rd << 7) | opcode

  private def encodeJ(imm: Int, rd: Int, opcode: Int): Int =
    (((imm >>> 20) & 0x1) << 31) | (((imm >>> 1) & 0x3ff) << 21) |
      (((imm >>> 11) & 0x1) << 20) | (((imm >>> 12) & 0xff) << 12) |
      (rd << 7) | opcode

  def isCompressed(instr: Int): Boolean =
    (instr & 0x3) != 0x3

  def expand(instr: Int): Int = {
    val quadrant = instr & 0x3
    val funct3 = bits(instr, 15, 13)

    (quadrant, funct3) match {
      case (0, 0) =>
        val imm = (bits(instr, 12, 11) << 4) | (bits(instr, 10, 7) << 6) |
          (bit(instr, 6) << 2) | (bit(instr, 5) << 3)
        val rd = rvcReg(bits(instr, 4, 2))
        if (imm == 0) illegal(instr) else encodeI(imm, 2, 0, rd, Opcode.AluImm)

      case (0, 2) =>
        val imm = (bit(instr, 5) << 6) | (bits(instr, 12, 10) << 3) | (bit(instr, 6) << 2)
        val rs1 = rvcReg(bits(instr, 9, 7))
        val rd = rvcReg(bits(instr, 4, 2))
        encodeI(imm, rs1, LoadStoreFunct3.LW, rd, Opcode.Load)

      case (0, 6) =>
        val imm = (bit(instr, 5) << 6) | (bits(instr, 12, 10) << 3) | (bit(instr, 6) << 2)
        val rs1 = rvcReg(bits(instr, 9, 7))
        val rs2 = rvcReg(bits(instr, 4, 2))
        encodeS(imm, rs2, rs1, LoadStoreFunct3.SW, Opcode.Store)

      case (1, 0) =>
        val imm = sext((bit(instr, 12) << 5) | bits(instr, 6, 2), 6)
        val rd = bits(instr, 11, 7)
        encodeI(imm, rd, AluFunct3.F3_ADD_SUB, rd, Opcode.AluImm)

      case (1, 1) =>
        encodeJ(cjImm(instr), 1, Opcode.Jal)

      case (1, 2) =>
        val imm = sext((bit(instr, 12) << 5) | bits(instr, 6, 2), 6)
        val rd = bits(instr, 11, 7)
        if (rd == 0) illegal(instr) else encodeI(imm, 0, AluFunct3.F3_ADD_SUB, rd, Opcode.AluImm)

      case (1, 3) =>
        val rd = bits(instr, 11, 7)
        if (rd == 2) {
          val imm = sext((bit(instr, 12) << 9) | (bit(instr, 6) << 4) |
            (bit(instr, 5) << 6) | (bits(instr, 4, 3) << 7) | (bit(instr, 2) << 5), 10)
          encodeI(imm, 2, AluFunct3.F3_ADD_SUB, 2, Opcode.AluImm)
        } else if (rd != 0) {
          val imm = sext((bit(instr, 12) << 17) | (bits(instr, 6, 2) << 12), 18)
          if (imm == 0) illegal(instr) else encodeU(imm, rd, Opcode.Lui)
        } else {
          illegal(instr)
        }

      case (1, 4) =>
        val rdRs1 = rvcReg(bits(instr, 9, 7))
        bits(instr, 11, 10) match {
          case 0 =>
            val shamt = (bit(instr, 12) << 5) | bits(instr, 6, 2)
            encodeI(shamt, rdRs1, AluFunct3.F3_SRL_SRA, rdRs1, Opcode.AluImm)
          case 1 =>
            val shamt = (bit(instr, 12) << 5) | bits(instr, 6, 2)
            encodeI(0x400 | shamt, rdRs1, AluFunct3.F3_SRL_SRA, rdRs1, Opcode.AluImm)
          case 2 =>
            val imm = sext((bit(instr, 12) << 5) | bits(instr, 6, 2), 6)
            encodeI(imm, rdRs1, AluFunct3.F3_AND, rdRs1, Opcode.AluImm)
          case 3 =>
            val rs2 = rvcReg(bits(instr, 4, 2))
            bits(instr, 6, 5) match {
              case 0 => encodeR(AluFunct7.SRA_SUB, rs2, rdRs1, AluFunct3.F3_ADD_SUB, rdRs1, Opcode.Alu)
              case 1 => encodeR(AluFunct7.DEFAULT, rs2, rdRs1, AluFunct3.F3_XOR, rdRs1, Opcode.Alu)
              case 2 => encodeR(AluFunct7.DEFAULT, rs2, rdRs1, AluFunct3.F3_OR, rdRs1, Opcode.Alu)
              case 3 => encodeR(AluFunct7.DEFAULT, rs2, rdRs1, AluFunct3.F3_AND, rdRs1, Opcode.Alu)
            }
        }

      case (1, 5) =>
        encodeJ(cjImm(instr), 0, Opcode.Jal)

      case (1, 6) =>
        val imm = cbImm(instr)
        val rs1 = rvcReg(bits(instr, 9, 7))
        encodeB(imm, 0, rs1, BranchFunct3.BEQ, Opcode.Branch)

      case (1, 7) =>
        val imm = cbImm(instr)
        val rs1 = rvcReg(bits(instr, 9, 7))
        encodeB(imm, 0, rs1, BranchFunct3.BNE, Opcode.Branch)

      case (2, 0) =>
        val shamt = (bit(instr, 12) << 5) | bits(instr, 6, 2)
        val rd = bits(instr, 11, 7)
        if (rd == 0) illegal(instr) else encodeI(shamt, rd, AluFunct3.F3_SLL, rd, Opcode.AluImm)

      case (2, 2) =>
        val imm = (bit(instr, 12) << 5) | (bits(instr, 6, 4) << 2) | (bits(instr, 3, 2) << 6)
        val rd = bits(instr, 11, 7)
        if (rd == 0) illegal(instr) else encodeI(imm, 2, LoadStoreFunct3.LW, rd, Opcode.Load)

      case (2, 4) =>
        val rdRs1 = bits(instr, 11, 7)
        val rs2 = bits(instr, 6, 2)
        (bit(instr, 12), rdRs1, rs2) match {
          case (0, 0, _) => illegal(instr)
          case (0, _, 0) => encodeI(0, rdRs1, 0, 0, Opcode.JalR)
          case (0, _, _) => encodeR(0, rs2, 0, 0, rdRs1, Opcode.Alu)
          case (1, 0, 0) => 0x00100073
          case (1, 0, _) => illegal(instr)
          case (1, _, 0) => encodeI(0, rdRs1, 0, 1, Opcode.JalR)
          case (1, _, _) => encodeR(0, rs2, rdRs1, 0, rdRs1, Opcode.Alu)
        }

      case (2, 6) =>
        val imm = (bits(instr, 12, 9) << 2) | (bits(instr, 8, 7) << 6)
        val rs2 = bits(instr, 6, 2)
        encodeS(imm, rs2, 2, LoadStoreFunct3.SW, Opcode.Store)

      case _ =>
        illegal(instr)
    }
  }

  private def cbImm(instr: Int): Int = {
    val raw = (bit(instr, 12) << 8) | (bits(instr, 11, 10) << 3) |
      (bits(instr, 6, 5) << 6) | (bits(instr, 4, 3) << 1) | (bit(instr, 2) << 5)
    sext(raw, 9)
  }

  private def cjImm(instr: Int): Int = {
    val raw = (bit(instr, 12) << 11) | (bit(instr, 11) << 4) |
      (bits(instr, 10, 9) << 8) | (bit(instr, 8) << 10) |
      (bit(instr, 7) << 6) | (bit(instr, 6) << 7) |
      (bits(instr, 5, 3) << 1) | (bit(instr, 2) << 5)
    sext(raw, 12)
  }

  private def illegal(instr: Int): Int =
    throw new IllegalArgumentException(f"Unsupported compressed instruction 0x$instr%04x")
}
