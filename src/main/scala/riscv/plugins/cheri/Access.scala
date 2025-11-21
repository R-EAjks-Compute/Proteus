package riscv.plugins.cheri

import riscv._

import spinal.core._
import riscv.BaseIsa.RV32E.xlen

class Access(stage: Stage)(implicit context: Context) extends Plugin[Pipeline] {
  object FieldSelect extends SpinalEnum {
    val PERM, TYPE, BASE, LEN, TAG, SEALED, OFFSET, ADDR = newElement()
  }

  object Modification extends SpinalEnum {
    val AND_PERM, SET_OFFSET, SET_ADDR, INC_OFFSET, SET_BOUNDS, SET_BOUNDS_EXACT, CLEAR_TAG =
      newElement()
  }

  object Data {
    object CGET extends PipelineData(Bool())
    object CFIELD extends PipelineData(FieldSelect())
    object CMODIFY extends PipelineData(Bool())
    object CMODIFICATION extends PipelineData(Modification())
    object IMM_IS_UNSIGNED extends PipelineData(Bool())
    object CMOVE extends PipelineData(Bool())
  }

  override def setup(): Unit = {
    pipeline.service[DecoderService].configure { config =>
      config.addDefault(
        Map(
          Data.CGET -> False,
          Data.CMODIFY -> False,
          Data.IMM_IS_UNSIGNED -> False,
          Data.CMOVE -> False
        )
      )

      val getters = Map(
        Opcodes.CGetPerm -> FieldSelect.PERM,
        Opcodes.CGetType -> FieldSelect.TYPE,
        Opcodes.CGetBase -> FieldSelect.BASE,
        Opcodes.CGetLen -> FieldSelect.LEN,
        Opcodes.CGetTag -> FieldSelect.TAG,
        Opcodes.CGetSealed -> FieldSelect.SEALED,
        Opcodes.CGetOffset -> FieldSelect.OFFSET,
        Opcodes.CGetAddr -> FieldSelect.ADDR
      )

      for ((opcode, selector) <- getters) {
        config.addDecoding(
          opcode,
          InstructionType.R_CxR,
          Map(
            Data.CGET -> True,
            Data.CFIELD -> selector
          )
        )
      }

      val modifiers = Seq(
        (Opcodes.CAndPerm, Modification.AND_PERM, InstructionType.R_CRC),
        (Opcodes.CSetOffset, Modification.SET_OFFSET, InstructionType.R_CRC),
        (Opcodes.CSetAddr, Modification.SET_ADDR, InstructionType.R_CRC),
        (Opcodes.CIncOffset, Modification.INC_OFFSET, InstructionType.R_CRC),
        (Opcodes.CIncOffsetImm, Modification.INC_OFFSET, InstructionType.I_CxC),
        (Opcodes.CSetBounds, Modification.SET_BOUNDS, InstructionType.R_CRC),
        (Opcodes.CSetBoundsExact, Modification.SET_BOUNDS_EXACT, InstructionType.R_CRC),
        (Opcodes.CSetBoundsImm, Modification.SET_BOUNDS, InstructionType.I_CxC),
        (Opcodes.CClearTag, Modification.CLEAR_TAG, InstructionType.R_CxC)
      )

      for ((opcode, modification, itype) <- modifiers) {
        config.addDecoding(
          opcode,
          itype,
          Map(
            Data.CMODIFY -> True,
            Data.CMODIFICATION -> modification
          )
        )
      }

      config.addDecoding(
        Opcodes.CSetBoundsImm,
        Map(
          Data.IMM_IS_UNSIGNED -> True
        )
      )

      config.addDecoding(
        Opcodes.CMove,
        InstructionType.R_CxC,
        Map(
          Data.CMOVE -> True
        )
      )
    }
  }

  override def build(): Unit = {
    stage plug new Area {
      import stage._

      when(arbitration.isValid) {
        when(value(Data.CGET)) {
          arbitration.rs1Needed := True
          val cap = value(context.data.CS1_DATA)

          when(!arbitration.isStalled) {
            def capMaxAddress(inAddr: UInt): UInt = {
              val maxAddress = UInt(config.xlen bits).setAll()
              val retAddr = UInt(config.xlen bits)

              when(inAddr > maxAddress) {
                retAddr := maxAddress
              } otherwise {
                retAddr := inAddr.resize(config.xlen)
              }
              retAddr
            }

            val rd = value(Data.CFIELD).mux(
              FieldSelect.PERM -> cap.perms.asIsaBits.asUInt.resized,
              FieldSelect.TYPE -> cap.otype.extendedValue,
              FieldSelect.BASE -> cap.base,
              FieldSelect.LEN -> capMaxAddress(cap.length),
              FieldSelect.TAG -> cap.tag.asUInt.resized,
              FieldSelect.SEALED -> (cap.tag && cap.isSealed).asUInt.resized,
              FieldSelect.OFFSET -> cap.offset,
              FieldSelect.ADDR -> cap.address
            )

            output(pipeline.data.RD_DATA) := rd
            output(pipeline.data.RD_DATA_VALID) := True
          }
        }

        when(value(Data.CMODIFY)) {
          arbitration.rs1Needed := True
          val cs = value(context.data.CS1_DATA)

          val rhs = UInt(config.xlen bits)

          when(value(pipeline.data.IMM_USED)) {
            when(value(Data.IMM_IS_UNSIGNED)) {
              rhs := value(pipeline.data.IMM)(11 downto 0).resized
            } otherwise {
              rhs := value(pipeline.data.IMM)
            }
          } otherwise {
            arbitration.rs2Needed := True
            rhs := value(pipeline.data.RS2_DATA)
          }

          val cd = RegCapability()
          cd := cs

          val exceptionHandler = pipeline.service[ExceptionService]

          def except(cause: ExceptionCause) = {
            exceptionHandler.except(stage, cause, CapIdx.gpcr(value(pipeline.data.RS1)))
          }

          when(!arbitration.isStalled) {
            switch(value(Data.CMODIFICATION)) {
              is(Modification.AND_PERM) {
                when(cs.isSealed) {
                  cd.tag := False
                }
                val newPerms = cs.perms.asIsaBits & rhs.asBits
                cd.perms.assignFromIsaBits(newPerms)
              }
              is(Modification.SET_OFFSET) {
                val newAddress = cs.base + rhs // TODO use IntAlu?
                val representable = cs.fastRepCheck(rhs, True)

                when(!representable || cs.isSealed) {
                  cd.tag := False
                }
                cd.address := newAddress
              }
              is(Modification.SET_ADDR) {
                val delta = rhs - cs.address
                // TODO: avoid above subtraction with special repCheck of setAddress in
                // https://github.com/CTSRD-CHERI/cheri-cap-lib/blob/master/CHERICC_Fat.bsv
                val representable = cs.fastRepCheck(delta, False)
                when(!representable || cs.isSealed) {
                  cd.tag := False
                }
                cd.address := rhs
              }
              is(Modification.INC_OFFSET) {
                val representable = cs.fastRepCheck(rhs, False)
                when(!representable || cs.isSealed) {
                  cd.tag := False
                }
                cd.address := cs.address + rhs // TODO use IntAlu?
              }
              is(Modification.SET_BOUNDS) {
                val (_, inBounds, retCap) = cs.setBoundsReturn(rhs)
                cd := retCap
                when(!inBounds || cs.isSealed) {
                  cd.tag := False
                }
              }
              is(Modification.SET_BOUNDS_EXACT) {
                val (exact, inBounds, retCap) = cs.setBoundsReturn(rhs)
                cd := retCap
                when(!(inBounds && exact) || cs.isSealed) {
                  cd.tag := False
                }
              }
              is(Modification.CLEAR_TAG) {
                cd.tag := False
              }
            }

            output(context.data.CD_DATA) := cd
            output(pipeline.data.RD_DATA_VALID) := True
          }
        }

        when(value(Data.CMOVE)) {
          arbitration.rs1Needed := True

          when(!arbitration.isStalled) {
            output(context.data.CD_DATA) := value(context.data.CS1_DATA)
            output(pipeline.data.RD_DATA_VALID) := True
          }
        }
      }
    }
  }
}
