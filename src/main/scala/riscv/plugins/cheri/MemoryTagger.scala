package riscv.plugins.cheri

import riscv._
import spinal.core._
import spinal.lib._
import spinal.lib.fsm._
import riscv.plugins.memory.Metadata
import riscv.plugins.memory.MetadataProvider

// noinspection ForwardReference
class MemoryTagger(memoryStart: BigInt, memorySize: BigInt)(implicit context: Context)
    extends MetadataProvider {
  assert(context.config.memBusWidth % context.clen == 0)
  private val tagBlockSize = context.config.memBusWidth / context.clen
  assert(memorySize % (context.config.memBusWidth / 8) == 0)
  private val numTagBlocks = memorySize / (context.config.memBusWidth / 8)

  case class MemoryTaggerComponent() extends Component {
    setDefinitionName("MemoryTagger")
    setName("memorytagger")
    val io = new Bundle {
      val address = in UInt (context.config.xlen bits)
      val wvalid = in Bool ()
      val write = in Bool ()
      val wmask = in Bits (context.config.dbusConfig.dataWidth / 8 bits)
      val wTagBlock = in UInt (tagBlockSize bits)
      val rvalid = in Bool ()
      val rTagBlock = out UInt (tagBlockSize bits)
    }

    val tags = Mem(Bits(tagBlockSize bits), wordCount = numTagBlocks)

    io.rTagBlock.assignDontCare()
    val tagIndex = ((io.address - memoryStart) >> log2Up(tagBlockSize / 8)).resized
    when(io.wvalid && io.write) {
      // determine which tags need to be updated in the block
      val maskRegions = io.wmask.subdivideIn(tagBlockSize slices)
      val tagWMask = maskRegions.map(m => m.orR).asBits
      // do masked write into tag memory
      tags.write(tagIndex, io.wTagBlock.asBits, mask = tagWMask)
    }
    when(io.rvalid && !io.write) {
      io.rTagBlock := tags(tagIndex).asUInt
    }

    def connectToBus(bus: MemBus): Unit = {
      io.address := bus.cmd.address
      io.wvalid := bus.cmd.valid
      io.write := bus.cmd.write
      io.wmask := bus.cmd.wmask
      val cmdTagBlock = bus.cmd.metadata.element(CapabilityTags)
      io.wTagBlock := cmdTagBlock.asInstanceOf[UInt]
      io.rvalid := bus.rsp.valid
      bus.rsp.metadata.element(CapabilityTags) := io.rTagBlock
    }
  }

  def build(dbus: MemBus): Component = {
    val tagger = new MemoryTaggerComponent()
    tagger.connectToBus(dbus)
    tagger
  }

  override def getKey = CapabilityTags

  override def getHardType = UInt(tagBlockSize bits)

}
