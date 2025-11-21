package riscv.plugins.memory

import riscv._
import spinal.core._
import collection.mutable.LinkedHashSet

class Lsu(addressStages: Set[Stage], loadStages: Seq[Stage], storeStage: Stage)
    extends Plugin[Pipeline]
    with LsuService {
  private var addressTranslator = new LsuAddressTranslator {
    override def translate(
        stage: Stage,
        address: UInt,
        operation: SpinalEnumCraft[LsuOperationType.type],
        width: SpinalEnumCraft[LsuAccessWidth.type]
    ): UInt = {
      address
    }
  }

  private var addressTranslatorChanged = false
  private var externalAddress: UInt = _
  private var externalStoreData: UInt = _
  var storeMetadata: Bundle with DynBundleAccess[Metadata] = _
  private var hasExternalOps = false

  private object DefaultLoadHandler extends LoadHandler {
    override def build(stage: Stage, address: UInt, rsp: MemBusRsp): Unit = {
      import stage._
      val result = UInt(config.xlen bits)
      result.assignDontCare()

      val membusAddressLsb = log2Up(config.memBusWidth / 8)
      val offset = address(membusAddressLsb - 1 downto 0) << 3

      val supportedWidths =
        LsuAccessWidth.elements.filter(w => LsuAccessWidth.getBitWidth(w) <= config.xlen)

      switch(value(Data.LSU_ACCESS_WIDTH)) {
        for (w <- supportedWidths) {
          is(w) {
            val bitWidth = LsuAccessWidth.getBitWidth(w) bits
            val rValue = UInt(bitWidth)
            rValue := rsp.rdata(offset, bitWidth)
            when(value(Data.LSU_IS_UNSIGNED)) {
              result := Utils.zeroExtend(rValue, config.xlen)
            } otherwise {
              result := Utils.signExtend(rValue, config.xlen)
            }
          }
        }
      }

      output(pipeline.data.RD_DATA) := result
      output(pipeline.data.RD_DATA_VALID) := True
    }
  }

  private object DefaultStoreHandler extends StoreHandler {
    override def build(stage: Stage, address: UInt): UInt = {
      val data = UInt(maxStoreWidth bits)
      val wValue = stage.value(pipeline.data.RS2_DATA).resized
      data := wValue

      switch(stage.value(Data.LSU_ACCESS_WIDTH)) {
        is(LsuAccessWidth.H) {
          val hValue = wValue(15 downto 0)

          when(address(1)) {
            data := (hValue << 16).resized
          } otherwise {
            data := hValue.resized
          }
        }
        is(LsuAccessWidth.B) {
          val bValue = wValue(7 downto 0)

          switch(address(1 downto 0).asBits) {
            is(B"00") {
              data := bValue.resized
            }
            is(B"01") {
              data := (bValue << 8).resized
            }
            is(B"10") {
              data := (bValue << 16).resized
            }
            is(B"11") {
              data := (bValue << 24).resized
            }
          }
        }
      }
      data
    }
  }

  private val externalLoadHandlers: LinkedHashSet[LoadHandler] = LinkedHashSet(DefaultLoadHandler)
  private val externalStoreHandlers: LinkedHashSet[StoreHandler] = LinkedHashSet(
    DefaultStoreHandler
  )
  private var maxStoreWidth = 0

  object Data {
    object LSU_OPERATION_TYPE extends PipelineData(LsuOperationType())
    object LSU_ACCESS_WIDTH extends PipelineData(LsuAccessWidth())
    object LSU_IS_UNSIGNED extends PipelineData(Bool())
    object LSU_EXTERNAL_ADDRESS extends PipelineData(Bool())
    object LSU_TARGET_ADDRESS extends PipelineData(UInt(config.xlen bits)) // TODO: Flow?
    object LSU_TARGET_VALID extends PipelineData(Bool())
    object LSU_STL_SPEC extends PipelineData(Bool())
    object LSU_PSF_ADDRESS extends PipelineData(UInt(config.xlen bits))
    object LSU_PSF_MISSPECULATION extends PipelineData(Bool())
    object LSU_EXTERNAL_DATA extends PipelineData(Bool())
    object LSU_LOAD_HANDLER extends PipelineData(UInt(2 bits))
    object LSU_STORE_HANDLER extends PipelineData(UInt(2 bits))
  }

  class DummyFormalService extends FormalService {
    override def lsuDefault(stage: Stage): Unit = ()
    override def lsuOnLoad(stage: Stage, addr: UInt, rmask: Bits, rdata: UInt): Unit = ()
    override def lsuOnStore(stage: Stage, addr: UInt, wmask: Bits, wdata: UInt): Unit = ()
    override def lsuOnMisaligned(stage: Stage): Unit = ()
  }

  override def addStore(
      opcode: MaskedLiteral,
      width: SpinalEnumCraft[LsuAccessWidth.type]
  ): Unit = {
    pipeline.service[DecoderService].configure { config =>
      config.addDecoding(
        opcode,
        Map(
          Data.LSU_OPERATION_TYPE -> LsuOperationType.STORE,
          Data.LSU_ACCESS_WIDTH -> width,
          Data.LSU_EXTERNAL_ADDRESS -> True,
          Data.LSU_TARGET_VALID -> False,
          Data.LSU_STL_SPEC -> False
        )
      )
    }

    hasExternalOps = true

    pipeline.service[IssueService].setDestinations(opcode, addressStages)
  }

  override def addStore(
      opcode: MaskedLiteral,
      dataHandler: StoreHandler,
      width: SpinalEnumElement[LsuAccessWidth.type],
      useExternalAddress: Boolean = false
  ): Unit = {
    externalStoreHandlers += dataHandler
    pipeline.service[DecoderService].configure { config =>
      config.addDecoding(
        opcode,
        Map(
          Data.LSU_OPERATION_TYPE -> LsuOperationType.STORE,
          Data.LSU_TARGET_VALID -> False,
          Data.LSU_EXTERNAL_DATA -> True,
          Data.LSU_STL_SPEC -> False,
          Data.LSU_EXTERNAL_ADDRESS -> Bool(useExternalAddress),
          Data.LSU_ACCESS_WIDTH -> width.craft(),
          Data.LSU_STORE_HANDLER -> U(externalStoreHandlers.iterator.indexOf(dataHandler))
        )
      )
    }
    maxStoreWidth = Math.max(LsuAccessWidth.getBitWidth(width), maxStoreWidth)
  }

  override def addLoad(
      opcode: MaskedLiteral,
      width: SpinalEnumCraft[LsuAccessWidth.type],
      unsigned: Boolean
  ): Unit = {
    pipeline.service[DecoderService].configure { config =>
      config.addDecoding(
        opcode,
        Map(
          Data.LSU_OPERATION_TYPE -> LsuOperationType.LOAD,
          Data.LSU_ACCESS_WIDTH -> width,
          Data.LSU_IS_UNSIGNED -> Bool(unsigned),
          Data.LSU_EXTERNAL_ADDRESS -> True,
          Data.LSU_TARGET_VALID -> False
        )
      )
    }

    hasExternalOps = true

    pipeline.service[IssueService].setDestinations(opcode, addressStages)
  }

  override def addLoad(
      opcode: MaskedLiteral,
      dataHandler: LoadHandler,
      width: SpinalEnumElement[LsuAccessWidth.type],
      useExternalAddress: Boolean = false
  ): Unit = {
    externalLoadHandlers += dataHandler
    pipeline.service[DecoderService].configure { config =>
      config.addDecoding(
        opcode,
        Map(
          Data.LSU_OPERATION_TYPE -> LsuOperationType.LOAD,
          Data.LSU_TARGET_VALID -> False,
          Data.LSU_EXTERNAL_DATA -> True,
          Data.LSU_EXTERNAL_ADDRESS -> Bool(useExternalAddress),
          Data.LSU_ACCESS_WIDTH -> width.craft(),
          Data.LSU_LOAD_HANDLER -> U(externalLoadHandlers.iterator.indexOf(dataHandler))
        )
      )
    }
  }

  override def setAddress(address: UInt): Unit = {
    externalAddress := address
  }

  override def setExternalStoreData(data: UInt): Unit = {
    externalStoreData := data
  }

  override def stage: Stage = addressStages.head // TODO: which one? needed?

  override def operation(stage: Stage): SpinalEnumCraft[LsuOperationType.type] = {
    stage.value(Data.LSU_OPERATION_TYPE)
  }

  override def operationOutput(stage: Stage): SpinalEnumCraft[LsuOperationType.type] = {
    stage.output(Data.LSU_OPERATION_TYPE)
  }
  override def operationOfBundle(bundle: Bundle with DynBundleAccess[PipelineData[Data]]): Data = {
    bundle.element(Data.LSU_OPERATION_TYPE.asInstanceOf[PipelineData[Data]])
  }
  override def addressOfBundle(bundle: Bundle with DynBundleAccess[PipelineData[Data]]): UInt = {
    bundle.elementAs[UInt](Data.LSU_TARGET_ADDRESS.asInstanceOf[PipelineData[Data]])
  }
  override def address(stage: Stage): UInt = {
    stage.output(Data.LSU_TARGET_ADDRESS)
  }
  override def addressValidOfBundle(
      bundle: Bundle with DynBundleAccess[PipelineData[Data]]
  ): Bool = {
    bundle.elementAs[Bool](Data.LSU_TARGET_VALID.asInstanceOf[PipelineData[Data]])
  }

  override def width(stage: Stage): SpinalEnumCraft[LsuAccessWidth.type] = {
    stage.value(Data.LSU_ACCESS_WIDTH)
  }

  override def widthOut(stage: Stage): SpinalEnumCraft[LsuAccessWidth.type] = {
    stage.output(Data.LSU_ACCESS_WIDTH)
  }

  override def width(
      bundle: Bundle with DynBundleAccess[PipelineData[Data]]
  ): SpinalEnumCraft[LsuAccessWidth.type] = {
    bundle.elementAs[SpinalEnumCraft[LsuAccessWidth.type]](
      Data.LSU_ACCESS_WIDTH.asInstanceOf[PipelineData[Data]]
    )
  }

  override def setup(): Unit = {
    maxStoreWidth = config.xlen
    for (addressStage <- addressStages) {
      addressStage plug new Area {
        val externalAddress = UInt(config.xlen bits).assignDontCare()
        Lsu.this.externalAddress = externalAddress
      }
    }

    val intAlu = pipeline.service[IntAluService]

    val allOpcodes32 = Seq(
      Opcodes.LB,
      Opcodes.LH,
      Opcodes.LW,
      Opcodes.LBU,
      Opcodes.LHU,
      Opcodes.SB,
      Opcodes.SH,
      Opcodes.SW
    )

    val allOpcodes64 = Seq(
      Opcodes64.LD,
      Opcodes64.LWU,
      Opcodes64.SD
    )

    val allOpcodes: Seq[MaskedLiteral] = if (config.xlen == 64) {
      allOpcodes64 ++ allOpcodes32
    } else {
      allOpcodes32
    }

    for (opcode <- allOpcodes) {
      intAlu.addOperation(opcode, intAlu.AluOp.ADD, intAlu.Src1Select.RS1, intAlu.Src2Select.IMM)
    }

    val decoder = pipeline.service[DecoderService]

    decoder.configure { dconfig =>
      dconfig.addDefault(
        Map(
          Data.LSU_OPERATION_TYPE -> LsuOperationType.NONE,
          Data.LSU_IS_UNSIGNED -> False,
          Data.LSU_EXTERNAL_ADDRESS -> False,
          Data.LSU_EXTERNAL_DATA -> False,
          Data.LSU_LOAD_HANDLER -> U(0),
          Data.LSU_STORE_HANDLER -> U(0)
        )
      )

      def addLoad(
          opcode: MaskedLiteral,
          width: SpinalEnumElement[LsuAccessWidth.type],
          unsigned: Bool
      ) = {
        dconfig.addDecoding(
          opcode,
          InstructionType.I,
          Map(
            Data.LSU_OPERATION_TYPE -> LsuOperationType.LOAD,
            Data.LSU_ACCESS_WIDTH -> width,
            Data.LSU_IS_UNSIGNED -> unsigned,
            Data.LSU_TARGET_VALID -> False
          )
        )

        pipeline.service[IssueService].setDestinations(opcode, addressStages)
      }

      addLoad(Opcodes.LW, LsuAccessWidth.W, False)
      addLoad(Opcodes.LH, LsuAccessWidth.H, False)
      addLoad(Opcodes.LB, LsuAccessWidth.B, False)
      addLoad(Opcodes.LHU, LsuAccessWidth.H, True)
      addLoad(Opcodes.LBU, LsuAccessWidth.B, True)

      if (config.xlen == 64) {
        addLoad(Opcodes64.LD, LsuAccessWidth.D, False)
        addLoad(Opcodes64.LWU, LsuAccessWidth.W, True)
      }

      def addStore(opcode: MaskedLiteral, width: SpinalEnumElement[LsuAccessWidth.type]) = {
        dconfig.addDecoding(
          opcode,
          InstructionType.S,
          Map(
            Data.LSU_OPERATION_TYPE -> LsuOperationType.STORE,
            Data.LSU_ACCESS_WIDTH -> width,
            Data.LSU_TARGET_VALID -> False
          )
        )

        pipeline.service[IssueService].setDestinations(opcode, addressStages)
      }

      addStore(Opcodes.SW, LsuAccessWidth.W)
      addStore(Opcodes.SH, LsuAccessWidth.H)
      addStore(Opcodes.SB, LsuAccessWidth.B)

      if (config.xlen == 64) {
        addStore(Opcodes64.SD, LsuAccessWidth.D)
      }
    }
  }

  override def build(): Unit = {
    for (addressStage <- addressStages) {
      addressStage plug new Area {
        import addressStage._

        val operation = value(Data.LSU_OPERATION_TYPE)
        val accessWidth = value(Data.LSU_ACCESS_WIDTH)
        val unsigned = value(Data.LSU_IS_UNSIGNED) // TODO: another hack
        val aluResult = value(pipeline.service[IntAluService].resultData)

        val inputAddress = if (hasExternalOps) {
          // We keep track of whether we have external loads/stores to 1) prevent LSU_IS_EXTERNAL_OP
          // from being added to the pipeline regs and 2) not generate this mux when not necessary
          // (although the latter might be optimized away at some point).
          value(Data.LSU_EXTERNAL_ADDRESS) ? externalAddress | aluResult
        } else {
          aluResult
        }

        val address = addressTranslator.translate(
          addressStage,
          inputAddress,
          operation,
          accessWidth
        )

        output(Data.LSU_TARGET_ADDRESS) := address
        when(operation === LsuOperationType.LOAD || operation === LsuOperationType.STORE) {
          output(Data.LSU_TARGET_VALID) := True
        }
      }
    }

    def checkAccessWidth(
        accessWidth: SpinalEnumCraft[LsuAccessWidth.type],
        address: UInt
    ) = {
      val misaligned = Bool()
      val baseMask = Bits(config.memBusWidth / 8 bits)
      val alignmentMask = LsuAccessWidth.getAlignmentMask(accessWidth).resized
      misaligned := (address & alignmentMask) =/= 0
      baseMask := LsuAccessWidth.getByteMask(accessWidth).asBits.resized

      (misaligned, baseMask)
    }

    def trap(cause: TrapCause, stage: Stage) = {
      val trapHandler = pipeline.service[TrapService]
      trapHandler.trap(stage, cause)
    }

    val memService = pipeline.service[MemoryService]
    val (loadDBuses, storeDBus) = memService.createInternalDBus(loadStages, storeStage)

    val formal = pipeline.serviceOption[FormalService] match {
      case Some(service) => service
      case None => new DummyFormalService
    }

    for (loadStage <- loadStages) {
      loadStage plug {
        formal.lsuDefault(loadStage)
      }
    }

    // Make sure we don't call lsuDefault twice when loadStage == storeStage (the second call will
    // overwrite everything that was written to the formal signals in the first stage that was
    // built).
    if (!loadStages.contains(storeStage)) {
      storeStage plug {
        formal.lsuDefault(storeStage)
      }
    }

    val loadAreas = loadStages.zipWithIndex.map { case (loadStage, stageIndex) =>
      loadStage plug new Area {

        import loadStage._

        val operation = value(Data.LSU_OPERATION_TYPE)
        val accessWidth = value(Data.LSU_ACCESS_WIDTH)
        val address = value(Data.LSU_TARGET_ADDRESS)
        val valid = value(Data.LSU_TARGET_VALID) // needed as a hack either way

        val dbusCtrl = new MemBusControl(loadDBuses(stageIndex))

        val isActive = operation === LsuOperationType.LOAD

        val isExternalData = value(Data.LSU_EXTERNAL_DATA)
        val (misaligned, baseMask) =
          checkAccessWidth(accessWidth, address)

        // TODO this becomes wrong for external data
        val mask = baseMask |<< address(1 downto 0)

        val busReady = Bool()
        val loadActive = RegInit(False)
        busReady := False

        when(isActive && misaligned) {
          if (pipeline.hasService[TrapService]) {
            trap(TrapCause.LoadAddressMisaligned(address), loadStage)

            formal.lsuOnMisaligned(loadStage)
          }
        }

        when(arbitration.isValid && !misaligned) {
          when(isActive) {
            val busAddress = address & U(0xfffffffcL)
            val valid = Bool()
            valid := False
            val fullValue = UInt(config.xlen bits).getZero
            busReady := dbusCtrl.isReady
            when(busReady) {
              loadActive := True
            }
            when(busReady || loadActive) {
              val tpl = dbusCtrl.read(busAddress)
              valid := tpl._1
              fullValue := tpl._2
            }
            when(valid) {
              loadActive := False
            }
            arbitration.isReady := valid

            switch(value(Data.LSU_LOAD_HANDLER)) {
              for ((handler, idx) <- externalLoadHandlers.zipWithIndex) {
                is(idx) {
                  handler.build(loadStage, address, loadDBuses(stageIndex).rsp)
                }
              }
            }
            formal.lsuOnLoad(loadStage, busAddress, mask, fullValue)
          }
        } otherwise {
          loadActive := False
          dbusCtrl.invalidate()
        }
      }
    }

    storeStage plug new Area {
      import storeStage._

      val externalStoreData = UInt(maxStoreWidth bits).assignDontCare()
      Lsu.this.externalStoreData = externalStoreData

      val metadata = config.dbusConfig.createMetadataBundle.assignDontCare()
      Lsu.this.storeMetadata = metadata

      val storeIndex = loadStages.indexOf(storeStage)

      val dbusCtrl = if (storeIndex != -1) {
        loadAreas(storeIndex).dbusCtrl
      } else {
        new MemBusControl(storeDBus)
      }

      val operation = value(Data.LSU_OPERATION_TYPE)
      val accessWidth = value(Data.LSU_ACCESS_WIDTH)
      val address = value(Data.LSU_TARGET_ADDRESS)
      val busAddress = address & U(0xfffffffcL)

      val isActive = operation === LsuOperationType.STORE

      val isExternalData = value(Data.LSU_EXTERNAL_DATA)
      val (misaligned, baseMask) =
        checkAccessWidth(accessWidth, address)

      val addressOffset = log2Up(config.memBusWidth / 8) - 1

      val mask = baseMask |<< address(addressOffset downto 0)

      when(isActive && misaligned) {
        if (pipeline.hasService[TrapService]) {
          trap(TrapCause.StoreAddressMisaligned(address), storeStage)

          formal.lsuOnMisaligned(storeStage)
        }
      }

      when(arbitration.isValid && !misaligned) {
        when(isActive) {
          arbitration.rs2Needed := True
          val data = UInt(maxStoreWidth bits)
          data := value(Data.LSU_STORE_HANDLER).muxListDc(
            externalStoreHandlers.toSeq.zipWithIndex.map(tpl =>
              (U(tpl._2), tpl._1.build(storeStage, address))
            )
          )
          // Position the data within the cache line
          val cacheLine = data << (busAddress(addressOffset downto 0) << 3)

          val accepted = dbusCtrl.write(busAddress, cacheLine.resized, mask, metadata)
          arbitration.isReady := accepted

          formal.lsuOnStore(storeStage, busAddress, mask, data)
        }
      }
    }
  }

  override def setAddressTranslator(translator: LsuAddressTranslator): Unit = {
    assert(!addressTranslatorChanged, "LsuAddressTranslator can only be set once")

    addressTranslator = translator
    addressTranslatorChanged = true
  }

  override def stlSpeculation(bundle: Bundle with DynBundleAccess[PipelineData[Data]]): Bool = {
    bundle.elementAs[Bool](Data.LSU_STL_SPEC.asInstanceOf[PipelineData[Data]])
  }

  override def stlSpeculation(stage: Stage): Bool = {
    stage.output(Data.LSU_STL_SPEC)
  }

  override def addStlSpeculation(bundle: DynBundle[PipelineData[Data]]): Unit = {
    bundle.addElement(
      Data.LSU_STL_SPEC.asInstanceOf[PipelineData[Data]],
      Data.LSU_STL_SPEC.dataType
    )
  }

  override def psfAddress(bundle: Bundle with DynBundleAccess[PipelineData[Data]]): UInt = {
    bundle.elementAs[UInt](Data.LSU_PSF_ADDRESS.asInstanceOf[PipelineData[Data]])
  }

  override def addPsfAddress(bundle: DynBundle[PipelineData[Data]]): Unit = {
    bundle.addElement(
      Data.LSU_PSF_ADDRESS.asInstanceOf[PipelineData[Data]],
      Data.LSU_PSF_ADDRESS.dataType
    )
  }

  override def psfMisspeculation(bundle: Bundle with DynBundleAccess[PipelineData[Data]]): Bool = {
    bundle.elementAs[Bool](Data.LSU_PSF_MISSPECULATION.asInstanceOf[PipelineData[Data]])
  }

  override def addPsfMisspeculation(bundle: DynBundle[PipelineData[Data]]): Unit = {
    bundle.addElement(
      Data.LSU_PSF_MISSPECULATION.asInstanceOf[PipelineData[Data]],
      Data.LSU_PSF_MISSPECULATION.dataType
    )
  }

  override def psfMisspeculationRegister: PipelineData[Data] =
    Data.LSU_PSF_MISSPECULATION.asInstanceOf[PipelineData[Data]]
}
