package riscv.plugins.cheri

import riscv._

import spinal.core._

class Lsu(addressStages: Set[Stage], loadStages: Seq[Stage], storeStage: Stage)(implicit
    context: Context
) extends Plugin[Pipeline] {
  object Data {
    object STORE_CAP extends PipelineData(Bool())
    object LOAD_CAP extends PipelineData(Bool())
    object USE_DDC_AUTH extends PipelineData(Bool())
    object AUTH_CAP extends PipelineData(PackedCapability())
    object AUTH_CAP_IDX extends PipelineData(CapIdx())
  }

  private class CapCheck(lsu: LsuService, stage: Stage) extends Area {
    private val cap = PackedCapability().assignDontCare()
    private val address = UInt(config.xlen bits).assignDontCare()
    private val operation = lsu.operation(stage)
    private val byteWidth = UInt(log2Up(context.clen / 8) + 1 bits).assignDontCare()
    private val exceptionCause = UInt(5 bits)
    exceptionCause := ExceptionCause.None.code

    when(operation =/= LsuOperationType.NONE) {
      // Exception priority
      // https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-951.pdf Table 3.4 p. 110
      when(!cap.tag) {
        except(ExceptionCause.TagViolation)
      } elsewhen (cap.isSealed) {
        except(ExceptionCause.SealViolation)
      } elsewhen (operation === LsuOperationType.LOAD && !cap.perms.load) {
        except(ExceptionCause.PermitLoadViolation)
      } elsewhen (operation === LsuOperationType.STORE && !cap.perms.store) {
        except(ExceptionCause.PermitStoreViolation)
      } elsewhen (operation === LsuOperationType.LOAD && stage.value(
        Data.LOAD_CAP
      ) && !cap.perms.loadCapability) {
        // This assumes cap.perms.load is set thanks to a previous check
        except(ExceptionCause.PermitLoadCapabilityViolation)
      } elsewhen (operation === LsuOperationType.STORE && stage.value(
        Data.STORE_CAP
      ) && !cap.perms.storeCapability) {
        // This assumes cap.perms.store is set thanks to a previous check
        except(ExceptionCause.PermitStoreCapabilityViolation)
      } elsewhen (address + byteWidth > cap.top) {
        except(ExceptionCause.LengthViolation)
      } elsewhen (address < cap.base) {
        except(ExceptionCause.LengthViolation)
      }
    }

    private def except(cause: ExceptionCause) = {
      exceptionCause := cause.code
    }

    def check(
        cap: Capability,
        address: UInt,
        byteWidth: UInt
    ): UInt = {
      assert(byteWidth.getBitsWidth <= this.byteWidth.getBitsWidth)

      this.cap.assignFrom(cap)
      this.address := address
      this.byteWidth := byteWidth.resized
      exceptionCause
    }
  }

  private var capChecks: Map[Stage, CapCheck] = Map()

  override def setup(): Unit = {
    val lsu = pipeline.service[LsuService]
    val capCheckStages =
      if (loadStages.contains(storeStage)) loadStages else (loadStages :+ storeStage)
    this.capChecks = (capCheckStages zip capCheckStages.map(s => s plug new CapCheck(lsu, s))).toMap

    val membusAddressLsb = log2Up(config.memBusWidth / 8)
    val capAddressLsb = log2Up(context.clen / 8)

    def checkAccessWidth(stage: Stage, address: UInt, misaligned: Bool, baseMask: Bits): Unit = {
      val isLoadCap = stage.value(Data.LOAD_CAP)
      val isStoreCap = stage.value(Data.STORE_CAP)
      when(isLoadCap || isStoreCap) {
        baseMask := (1 << context.clen / 8) - 1
        misaligned := (address & baseMask.asUInt.resized) =/= 0
      }
    }

    def getTagIdx(address: UInt): UInt = {
      address(membusAddressLsb - 1 downto capAddressLsb)
    }

    object CapLoadHandler extends lsu.LoadHandler {
      override def build(loadStage: Stage, address: UInt, rsp: MemBusRsp): Unit = {
        import loadStage._
        val tagIdx = getTagIdx(address)
        val offset = tagIdx << context.clen
        val capData = rsp.rdata(offset, context.clen bits)
        val capTag = rsp.metadata.element(CapabilityTags).asBits(tagIdx)

        val cap = MemCapability()
        cap.assignValue(capData)
        cap.tag := capTag

        output(context.data.CD_DATA).assignFrom(cap)
        output(pipeline.data.RD_DATA_VALID) := True
      }
    }

    object CapStoreHandler extends lsu.StoreHandler {
      def build(storeStage: Stage, address: UInt): UInt = {
        val tagIdx = getTagIdx(address)
        val regCap = storeStage.value(context.data.CS2_DATA)
        val memCap = MemCapability().assignFrom(regCap)
        lsu.storeMetadata.element(CapabilityTags) := (U(1) << tagIdx).resized

        memCap.value
      }
    }

    pipeline.service[DecoderService].configure { config =>
      val lsu = pipeline.service[LsuService]

      config.addDefault(
        Map(
          Data.STORE_CAP -> False,
          Data.LOAD_CAP -> False,
          Data.USE_DDC_AUTH -> True
        )
      )

      config.addDecoding(
        Opcodes.SC_CAP,
        InstructionType.R_CCx,
        Map(
          Data.STORE_CAP -> True,
          Data.USE_DDC_AUTH -> False
        )
      )
      lsu.addStore(
        Opcodes.SC_CAP,
        CapStoreHandler.asInstanceOf[lsu.StoreHandler],
        LsuAccessWidth.D,
        useExternalAddress = true
      )

      config.addDecoding(
        Opcodes.LC_CAP,
        InstructionType.R_CxC,
        Map(
          Data.LOAD_CAP -> True,
          Data.USE_DDC_AUTH -> False
        )
      )
      lsu.addLoad(
        Opcodes.LC_CAP,
        CapLoadHandler.asInstanceOf[lsu.LoadHandler],
        LsuAccessWidth.D,
        useExternalAddress = true
      )

      config.addDecoding(
        Opcodes.SC,
        InstructionType.S_RCx,
        Map(
          Data.STORE_CAP -> True
        )
      )

      lsu.addStore(
        Opcodes.SC,
        CapStoreHandler.asInstanceOf[lsu.StoreHandler],
        LsuAccessWidth.D
      )

      config.addDecoding(
        Opcodes.LC,
        InstructionType.I_RxC,
        Map(
          Data.LOAD_CAP -> True
        )
      )

      lsu.addLoad(
        Opcodes.LC,
        CapLoadHandler.asInstanceOf[lsu.LoadHandler],
        LsuAccessWidth.D
      )

      def addDataLoadCap(
          opcode: MaskedLiteral,
          width: SpinalEnumElement[LsuAccessWidth.type],
          unsigned: Boolean
      ) = {
        config.addDecoding(
          opcode,
          InstructionType.R_CxR,
          Map(Data.USE_DDC_AUTH -> False)
        )

        lsu.addLoad(opcode, width, unsigned)
      }

      addDataLoadCap(Opcodes.LB_CAP, LsuAccessWidth.B, unsigned = false)
      addDataLoadCap(Opcodes.LH_CAP, LsuAccessWidth.H, unsigned = false)
      addDataLoadCap(Opcodes.LW_CAP, LsuAccessWidth.W, unsigned = false)
      addDataLoadCap(Opcodes.LBU_CAP, LsuAccessWidth.B, unsigned = true)
      addDataLoadCap(Opcodes.LHU_CAP, LsuAccessWidth.H, unsigned = true)

      def addDataStoreCap(opcode: MaskedLiteral, width: SpinalEnumElement[LsuAccessWidth.type]) = {
        config.addDecoding(
          opcode,
          InstructionType.R_CRx,
          Map(Data.USE_DDC_AUTH -> False)
        )

        lsu.addStore(opcode, width)
      }

      addDataStoreCap(Opcodes.SB_CAP, LsuAccessWidth.B)
      addDataStoreCap(Opcodes.SH_CAP, LsuAccessWidth.H)
      addDataStoreCap(Opcodes.SW_CAP, LsuAccessWidth.W)
    }
    val intAlu = pipeline.service[IntAluService]

    val aluOpcodes = Seq(
      Opcodes.SC,
      Opcodes.LC
    )

    for (opcode <- aluOpcodes) {
      intAlu.addOperation(opcode, intAlu.AluOp.ADD, intAlu.Src1Select.RS1, intAlu.Src2Select.IMM)
    }
  }

  override def build(): Unit = {
    val lsu = pipeline.service[LsuService]

    storeStage plug new Area {
      when(!storeStage.value(Data.STORE_CAP)) {
        lsu.storeMetadata.element(CapabilityTags) := U(0).resized
        lsu.storeMetadata.element(CapabilityTags).allowOverride
      }
    }

    for (addressStage <- addressStages) {
      addressStage plug new Area {
        import addressStage._

        val ddc = pipeline.service[ScrService].getDdc(addressStage)
        val cs1 = value(context.data.CS1_DATA)

        when(value(Data.USE_DDC_AUTH)) {
          output(Data.AUTH_CAP).assignFrom(ddc)
          output(Data.AUTH_CAP_IDX) := CapIdx.scr(ScrIndex.DDC)
        } otherwise {
          output(Data.AUTH_CAP).assignFrom(cs1)
          output(Data.AUTH_CAP_IDX) := CapIdx.gpcr(value(pipeline.data.RS1))
          lsu.setAddress(cs1.address)
        }
      }
    }

    for ((stage, capCheck) <- this.capChecks) {
      val isLoadStage = loadStages contains stage
      val isStoreStage = storeStage == stage
      val activeCondition: SpinalEnumCraft[LsuOperationType.type] => Bool = { operation =>
        if (isLoadStage & isStoreStage)
          (operation === LsuOperationType.LOAD) || (operation === LsuOperationType.STORE)
        else if (isLoadStage) (operation === LsuOperationType.LOAD)
        else if (isStoreStage) (operation === LsuOperationType.STORE)
        else False
      }

      stage plug new Area {
        import stage._
        val lsu = pipeline.service[LsuService]

        val operation = lsu.operation(stage)
        val isActive = activeCondition(operation)

        when(arbitration.isValid && isActive) {
          val authCap = value(Data.AUTH_CAP)
          val address = lsu.address(stage)
          val byteWidth = UInt(log2Up(context.clen / 8) + 1 bits)
          byteWidth := LsuAccessWidth.getByteWidth(lsu.width(stage)).resized

          val cause = capCheck.check(authCap, address, byteWidth)

          // TODO stop execution of stage on trap
          when(cause =/= ExceptionCause.None.code) {
            val handler = pipeline.service[ExceptionHandler]
            handler.except(stage, cause, value(Data.AUTH_CAP_IDX))
          }
        }
      }
    }
  }
}
