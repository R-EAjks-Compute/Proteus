package riscv

import spinal.core._
import spinal.lib._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

object Utils {
  def signExtend[T <: BitVector](data: T, width: Int): T = {
    val dataWidth = data.getBitsWidth
    assert(dataWidth <= width && dataWidth > 0)

    (B((width - 1 - dataWidth downto 0) -> data(dataWidth - 1)) ## data)
      .as(data.clone().setWidth(width))
  }

  def zeroExtend[T <: BitVector](data: T, width: Int): T = {
    val dataWidth = data.getBitsWidth
    assert(dataWidth <= width && dataWidth > 0)

    (B((width - 1 - dataWidth downto 0) -> False) ## data).as(data.clone().setWidth(width))
  }

  def twosComplement(data: UInt): UInt = ~data + 1

  def delay(cycles: Int)(logic: => Unit) = {
    assert(cycles >= 0)

    val delayCounter = Counter(cycles + 1)

    when(delayCounter.willOverflowIfInc) {
      logic
    }

    delayCounter.increment()
  }

  def outsideConditionScope[T](rtl: => T): T = {
    val body = Component.current.dslBody
    val ctx = body.push()
    val swapContext = body.swap()
    val ret = rtl
    ctx.restore()
    swapContext.appendBack()
    ret
  }

  implicit class StreamExtensions[T <: Data](stream: Stream[T]) {
    def stage(stagesCount: Int): Stream[T] = {
      stagesCount match {
        case 0 => stream
        case _ => stream.stage().stage(stagesCount - 1)
      }
    }
  }

  // copy of spinal.lib implementation.
  // When spinal.lib gets updated you can use that one instead
  /** Counts the number of consecutive zero bits starting from the MSB. */
  object CountLeadingZeroes {
    // Inspired by https://electronics.stackexchange.com/a/649761
    def apply(in: Bits): UInt = {
      val padLen = (1 << log2Up(in.getWidth)) - in.getWidth
      if (in.getWidth == 0) U(0)
      else if (in.getWidth == 1) ~in.asUInt
      else if (padLen != 0) {
        return CountLeadingZeroes(B(0, padLen bits) ## in) - padLen
      } else {
        val w = in.getWidth // input width
        assert(w % 2 == 0 && w > 0, s"cannot do clz for width $w")
        val ow = log2Up(w) + 1 // output width
        val olrw = ow - 1 // output width of halves

        val clzL = CountLeadingZeroes(in(w / 2, w / 2 bits))
        val clzR = CountLeadingZeroes(in(0, w / 2 bits))
        val first = clzL(olrw - 1) & clzR(olrw - 1)
        val mux = Mux(
          ~clzL(olrw - 1),
          U("0") ## clzL(0, olrw - 1 bits),
          (~clzR(olrw - 1)) ## clzR(0, olrw - 1 bits)
        )
        (first ## mux).asUInt
      }
    }
  }
}

trait DynBundleAccess[KeyType] {
  def element(key: KeyType): Data

  def elementAs[T <: Data](key: KeyType): T = {
    element(key).asInstanceOf[T]
  }
}

class DynBundle[KeyType] {
  private val elementsMap = mutable.Map[KeyType, Data]()

  val keys: Iterable[KeyType] = elementsMap.keys

  def addElement[T <: Data](key: KeyType, hardType: HardType[T]) = {
    val data = hardType()
    elementsMap(key) = data
  }

  def createBundle: Bundle with DynBundleAccess[KeyType] = {
    class NewBundle extends Bundle with DynBundleAccess[KeyType] {
      private val elementsMap = DynBundle.this.elementsMap.map { case (key, data) =>
        val clonedData = cloneOf(data)
        clonedData.parent = this

        if (OwnableRef.proposal(clonedData, this)) {
          clonedData.setPartialName(key.toString, Nameable.DATAMODEL_WEAK)
        }

        (key, clonedData)
      }

      override val elements: ArrayBuffer[(String, Data)] = elementsMap
        .map { case (key, data) =>
          (key.toString, data)
        }
        .toSeq
        .to[mutable.ArrayBuffer]

      override def element(key: KeyType): Data = {
        elementsMap(key)
      }

      override def clone(): Bundle = {
        new NewBundle
      }
    }

    new NewBundle
  }
}
