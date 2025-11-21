package riscv.plugins.cheri

import spinal.core._
import riscv.Utils

/* CHERI CONCENTRATE, 64-bit format
63____________________52___51___50_____47__46_45________________40_39___________________32
|                       |      |         |   |                    |                      |
|          perms        | flag |  otype  | 0 |            top<5:0>|             base<7:0>| Exp0
|          perms        |      |         | 1 |     top<5:3>|e<5:3>|      base<7:3>|e<2:0>| EmbeddedExp
|_______________________|______|_________|___|____________________|______________________|
31_______________________________________________________________________________________0
|                                                                                        |
|                                      address                                           |
|________________________________________________________________________________________|

For 128bit format see
https://github.com/CTSRD-CHERI/cheri-cap-lib/blob/93a22d303de2ec9bc263f128dd3592274a78f74e/CHERICC_Fat.bsv#L886
 */

trait Permissions {
  // https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-951.pdf Table 3.1 p. 75
  // Some permissions are missing
  def execute: Bool
  def load: Bool
  def store: Bool
  def loadCapability: Bool
  def storeCapability: Bool
  def seal: Bool
  def cinvoke: Bool
  def unseal: Bool
  def accessSystemRegisters: Bool

  def setAll(value: Bool): Unit = {
    execute := value
    load := value
    store := value
    loadCapability := value
    storeCapability := value
    seal := value
    cinvoke := value
    unseal := value
    accessSystemRegisters := value
  }

  def allowAll(): Unit = setAll(True)
  def allowNone(): Unit = setAll(False)

  def asIsaBits: Bits = {
    B"0" ## accessSystemRegisters ## unseal ## cinvoke ## seal ## B"0" ##
      storeCapability ## loadCapability ## store ## load ## execute ## B"0" resized
  }

  def assignFromIsaBits(bits: Bits): Unit = {
    execute := bits(1)
    load := bits(2)
    store := bits(3)
    loadCapability := bits(4)
    storeCapability := bits(5)
    seal := bits(7)
    cinvoke := bits(8)
    unseal := bits(9)
    accessSystemRegisters := bits(10)
  }

  def assignFrom(other: Permissions): Unit = {
    execute := other.execute
    load := other.load
    store := other.store
    loadCapability := other.loadCapability
    storeCapability := other.storeCapability
    seal := other.seal
    cinvoke := other.cinvoke
    unseal := other.unseal
    accessSystemRegisters := other.accessSystemRegisters
  }
}

case class PackedPermissions() extends Bundle with Permissions {
  override val execute = Bool()
  override val load = Bool()
  override val store = Bool()
  override val loadCapability = Bool()
  override val storeCapability = Bool()
  override val seal = Bool()
  override val cinvoke = Bool()
  override val unseal = Bool()
  override val accessSystemRegisters = Bool()
}

case class ObjectType(implicit context: Context) extends Bundle {
  // https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-951.pdf Table 3.2 p. 78
  val value = UInt(context.otypeLen bits)

  def extendedValue: UInt = {
    val xlen = context.config.xlen
    isSealed ? value.resize(xlen bits) | UInt(xlen bits).setAll()
  }

  def unseal(): Unit = value.setAll()
  def isSealed: Bool = value <= context.maxOtype
  def hasReservedOType: Bool = value > context.maxOtype
}

trait Capability {

  def xlen: Int

  def mlen: Int

  def explen: Int

  def halfExplen: Int = { explen / 2 }

  def resetExp: Int = xlen - mlen + 2;

  def tag: Bool

  def embeddedExp: Bool

  def compressedBase: UInt // TODO maybe change to bits

  def compressedTop: UInt

  def address: UInt

  def exp: UInt = {
    val resExp = UInt(explen bits)
    when(!embeddedExp) {
      resExp := 0
    } otherwise {
      resExp := (compressedTop.resize(halfExplen) ## compressedBase.resize(halfExplen)).asUInt
    }
    resExp
  }

  def clampedExp: UInt = {
    val e = UInt(explen bits)
    when(exp > resetExp) {
      e := resetExp
    } otherwise {
      e := exp
    }
    e
  }

  def addrBits: Bits = {
    (address >> this.exp).asBits.resize(mlen)
  }

  def topBits: Bits = {
    val out = Bits(mlen bits)
    when(!embeddedExp) {
      out := compressedTop.asBits
    } otherwise {
      out := compressedTop.asBits.resizeLeft(mlen - halfExplen) ## B(0, halfExplen bits)
    }
    out
  }

  def baseBits: Bits = {
    val out = Bits(mlen bits)
    when(!embeddedExp) {
      out := compressedBase.asBits
    } otherwise {
      out := compressedBase.asBits.resizeLeft(mlen - halfExplen) ## B(0, halfExplen bits)
    }
    out
  }

  def getCorrections: (SInt, SInt) = {
    val tb = topBits.resizeLeft(3).asUInt
    val bb = baseBits.resizeLeft(3).asUInt
    val ab = addrBits.resizeLeft(3).asUInt
    val repBound = bb - 1 // B"001".
    val topHi = tb < repBound;
    val baseHi = bb < repBound;
    val addrHi = ab < repBound;

    val baseCorrection = SInt(2 bits)
    when(baseHi === addrHi) {
      baseCorrection := 0
    } elsewhen (baseHi && !addrHi) {
      baseCorrection := 1
    } otherwise {
      baseCorrection := -1
    }

    val topCorrection = SInt(2 bits)
    when(topHi === addrHi) {
      topCorrection := 0
    } elsewhen (topHi && !addrHi) {
      topCorrection := 1
    } otherwise {
      topCorrection := -1
    }

    (baseCorrection, topCorrection)
  }

  def base: UInt = {
    val baseCorrection = getCorrections._1
    val addBase =
      (baseCorrection ## baseBits).asSInt.resize(xlen) |<< clampedExp // clamp Exp to resetExp
    val mask = S(-1, (xlen - mlen) bits).asBits |<< clampedExp
    val ret =
      ((address.asBits.resizeLeft(xlen - mlen) & mask) ## U(0, mlen bits)).asUInt + addBase.asUInt
    ret
  }

  def top: UInt = {
    val (baseCorrection, topCorrection) = getCorrections
    val topBitsAndImplied = topCorrection ## topBits

    val addTop = SInt(xlen + 1 bits)
    addTop := (topCorrection ## topBits).asSInt.resize(
      xlen + 1
    ) |<< clampedExp // clamp Exp to resetExp

    val mask = S(-1, xlen + 1 - mlen bits).asBits |<< clampedExp
    val ret = UInt(xlen + 1 bits)
    ret := (((B"0" ## address).resizeLeft(xlen + 1 - mlen) & mask) ## U(
      0,
      mlen bits
    )).asUInt + addTop.asUInt

    val topTip = ret.asBits.resizeLeft(2).asUInt // 2 msb's
    val botTip = (B"0" ## base.msb).asUInt

    val msb = Bool
    when((clampedExp < resetExp - 1) && ((topTip - botTip) > 1)) {
      msb := !ret.msb
    } otherwise {
      msb := ret.msb
    }

    return (msb ## ret.resize(xlen)).asUInt // 33bit
  }

  def length: UInt = top - base
  def offset: UInt = address - base
  def perms: Permissions
  def otype: ObjectType

  def hasOffset: Boolean = true

  def isSealed: Bool = otype.isSealed

  def hasReservedOType: Bool = otype.hasReservedOType

  def assignFrom(other: Capability): this.type = {
    tag := other.tag
    compressedBase := other.compressedBase
    compressedTop := other.compressedTop
    embeddedExp := other.embeddedExp
    perms.assignFrom(other.perms)
    otype := other.otype

    if (hasOffset && other.hasOffset) {
      address := other.address
    }

    this
  }

  def assignRoot(): this.type = {
    tag := True
    perms.allowAll()
    otype.unseal()
    assignNullBounds()
    address := 0

    this
  }

  // Null is Root without perms and untagged
  def assignNull(): this.type = {
    tag := False
    perms.allowNone()
    otype.unseal()
    assignNullBounds()
    address := 0

    this
  }

  private def assignNullBounds(): this.type = {
    embeddedExp := True

    // add resetExp to compressedBase and compressedTop
    // ugly scala bit string manipulation because elements of
    // ROM initialContent in RegisterFile should be literal values
    val botExpBinStr = resetExp.toBinaryString.takeRight(halfExplen)
    val topExpBinStr = resetExp.toBinaryString.dropRight(halfExplen)
    val tlen = topExpBinStr.length()
    compressedBase :=
      U(BigInt(botExpBinStr, 2), mlen bits)
    compressedTop :=
      U(BigInt("01" + "0" * (mlen - tlen - 2) + topExpBinStr, 2), mlen bits)

    this
  }
}

class PackedCapabilityFields(hasOffset: Boolean = true)(implicit context: Context) extends Bundle {
  private val xlen = context.config.xlen
  val embeddedExp = Bool()
  val compressedBase = UInt(context.mlen bits)
  val compressedTop = UInt(context.mlen bits)
  // val offset = if (hasOffset) UInt(xlen bits) else null
  val address = if (hasOffset) UInt(xlen bits) else null
  val perms = PackedPermissions()
  val otype = ObjectType()
}

object PackedCapabilityFields {
  def getBitsWidth(hasOffset: Boolean = true)(implicit context: Context): Int = {
    val fields = new PackedCapabilityFields(hasOffset)
    fields.getBitsWidth
  }
}

case class PackedCapability(override val hasOffset: Boolean = true)(implicit context: Context)
    extends PackedCapabilityFields(hasOffset)
    with Capability {

  override def xlen: Int = context.config.xlen

  override def mlen: Int = context.mlen

  override def explen: Int = context.expLen

  override val tag = Bool()

}

object PackedCapability {
  def Root(hasOffset: Boolean = true)(implicit context: Context): PackedCapability = {
    PackedCapability(hasOffset).assignRoot()
  }

  def Root(implicit context: Context): PackedCapability = Root(true)

  def Null(hasOffset: Boolean = true)(implicit context: Context): PackedCapability = {
    PackedCapability(hasOffset).assignNull()
  }

  def Null(implicit context: Context): PackedCapability = Null(true)
}

case class RegCapability(implicit context: Context) extends PackedCapabilityFields with Capability {
  private val padding = Bits(context.clen - PackedCapabilityFields.getBitsWidth() bits) //

  override def xlen: Int = context.config.xlen

  override def mlen: Int = context.mlen

  override def explen: Int = context.expLen

  override val tag = Bool()

  assert(getBitsWidth == context.clen + 1)

  // based of representability check incOffset function in
  // https://github.com/CTSRD-CHERI/cheri-cap-lib/blob/master/CHERICC_Fat.bsv
  def fastRepCheck(offset: UInt, setOffset: Bool): Bool = {
    val ii = offset.asSInt

    // The inRange test
    val signBits = ii.msb.asSInt.resize(xlen - mlen)
    val highOffsetBits = ii.asBits.resizeLeft(xlen - mlen)
    val highBitsFilter = IntToSInt(-1).resize(xlen - mlen) |<< exp
    val highOffsetBits2 = (highOffsetBits ^ signBits.asBits) & highBitsFilter.asBits
    val inRange = (highOffsetBits2 === 0)

    // The inLimits test
    val posInc = ii.msb === False

    val toBounds_A = U(B"111" ## baseBits.resize(mlen - 3)) - U(B"000" ## baseBits.resize(mlen - 3))
    val toBoundsM1_A = U(B"110" ## ~baseBits.resize(mlen - 3))

    val offsetBits = (ii >> exp).resize(mlen).asUInt
    val repBoundBits = (baseBits.asBits.resizeLeft(3).asUInt - 1) ## B(0, mlen - 3 bits)

    val toBounds_B = repBoundBits.asUInt - addrBits.asUInt
    val toBoundsM1_B = repBoundBits.asUInt + ~addrBits.asUInt

    val toBounds = UInt(mlen bits)
    when(setOffset) {
      toBounds := toBounds_A
    } otherwise {
      toBounds := toBounds_B
    }

    val toBoundsM1 = UInt(mlen bits)
    when(setOffset) {
      toBoundsM1 := toBoundsM1_A
    } otherwise {
      toBoundsM1 := toBoundsM1_B
    }

    val addrAtRepBound = !setOffset && (repBoundBits === addrBits)

    // Implement the inLimit test
    val inLimits = False
    when(posInc) {
      when(setOffset) {
        inLimits := offsetBits <= toBoundsM1
      } otherwise {
        inLimits := offsetBits < toBoundsM1
      }
    } otherwise {
      inLimits := (offsetBits >= toBounds) && !addrAtRepBound
    }

    // Complete representable bounds check
    (inRange && inLimits) || (exp >= (resetExp - 2))
  }

  // based of SetBoundsReturn in
  // https://github.com/CTSRD-CHERI/cheri-cap-lib/blob/master/CHERICC_Fat.bsv
  def setBoundsReturn(inLength: UInt): (Bool, Bool, RegCapability) = {

    // Set all bits below MSB to 1
    object SmearMSBRight {
      def apply(input: Bits): Bits = {
        val nbOfLZ = Utils.CountLeadingZeroes(input)
        val allOnes = B"1" #* input.getWidth
        val res = ~(allOnes |<< (U(input.getWidth) - nbOfLZ))
        return res
      }
    }

    // renaming for readability
    val capAddrPlus2 = xlen + 2

    // maybe at these to cap interface?
    val tb = this.topBits.resizeLeft(3).asUInt
    val bb = this.baseBits.resizeLeft(3).asUInt
    val ab = this.addrBits.resizeLeft(3).asUInt
    val repBound = bb - 1 // B"001".
    val topHi = tb < repBound;
    val baseHi = bb < repBound;
    val addrHi = ab < repBound;

    // Find new exponent by finding the index of the most significant bit of the
    // length, or counting leading zeros in the high bits of the length, and
    // substracting them to the CapAddr width (taking away the bottom MW-1 bits:
    // trim (MW-1) bits from the bottom of length since any length with a
    // significance that small will yield an exponent of zero).

    val lengthMSBs = inLength.asBits.resizeLeft(xlen - (mlen - 1))
    val zeros = Utils.CountLeadingZeroes(lengthMSBs).resize(explen)
    // Adjust resetExp by one since it's scale reaches 1-bit greater than a
    // 64-bit length can express.
    val maxZero = (zeros === (resetExp - 1))
    val intExp = !(maxZero && (inLength(mlen - 2) === False))
    // Do this without subtraction
    val e1 = ((resetExp - 1) - zeros).resize(explen)
    // Derive new base bits by extracting MW bits from the capability address
    // starting at the new exponent's position.
    val base = B"00" ## this.address
    val newBaseBits = (base >> e1).resize(mlen + 1)

    // Derive new top bits by extracting MW bits from the capability address +
    // requested length, starting at the new exponent's position, and rounding up
    // if significant bits are lost in the process.
    val len = B"00" ## inLength
    val top = (base.asUInt + len.asUInt).asBits

    // Create a mask with all bits set below the MSB of length and then masking
    // all bits below the mantissa bits.
    val lmask = SmearMSBRight(len.resize(capAddrPlus2))
    // The shift amount required to put the most significant set bit of the len
    // just above the bottom HalfExpW bits that are taken by the exp.
    val shiftAmount = (mlen - 2) - halfExplen;

    // Calculate all values associated with E=e (e not rounding up)
    // Round up considering the stolen HalfExpW exponent bits if required
    val newTopBits = (top >> e1).resize(mlen + 1).asBits
    // Check if non-zero bits were lost in the low bits of top, either in the 'e'
    // shifted out bits or in the HalfExpW bits stolen for the exponent
    // Shift by MW-1 to move MSB of mask just below the mantissa, then up
    // HalfExpW more to take in the bits that will be lost for the exponent when
    // it is non-zero.
    val lmaskLor = (lmask |>> shiftAmount + 1)
    val lmaskLo = (lmask |>> shiftAmount)
    // For the len, we're not actually losing significance since we're not
    // storing it, we just want to know if any low bits are non-zero so that we
    // will know if it will cause the total length to round up.
    val lostSignificantLen = (len & lmaskLor) =/= 0 && intExp
    val lostSignificantTop = (top & lmaskLor) =/= 0 && intExp
    // Check if non-zero bits were lost in the low bits of base, either in the
    // 'e' shifted out bits or in the HalfExpW bits stolen for the exponent
    val lostSignificantBase = (base & lmaskLor) =/= 0 && intExp;

    // Calculate all values associated with E=e+1 (e rounding up due to msb of L
    // increasing by 1) This value is just to avoid adding later.
    val newTopBitsHigher = newTopBits.resizeLeft(mlen)
    // Check if non-zero bits were lost in the low bits of top, either in the 'e'
    // shifted out bits or in the HalfExpW bits stolen for the exponent Shift by
    // MW-1 to move MSB of mask just below the mantissa, then up HalfExpW more to
    // take in the bits that will be lost for the exponent when it is non-zero.
    val lostSignificantTopHigher = (top & lmaskLo) =/= 0 && intExp
    // Check if non-zero bits were lost in the low bits of base, either in the
    // 'e' shifted out bits or in the HalfExpW bits stolen for the exponent
    val lostSignificantBaseHigher = (base & lmaskLo) =/= 0 && intExp;
    // If either base or top lost significant bits and we wanted an exact
    // setBounds, void the return capability

    // We need to round up Exp if the msb of length will increase.
    // We can check how much the length will increase without looking at the
    // result of adding the length to the base.  We do this by adding the lower
    // bits of the length to the base and then comparing both halves (above and
    // below the mask) to zero.  Either side that is non-zero indicates an extra
    // "1" that will be added to the "mantissa" bits of the length, potentially
    // causing overflow.  Finally check how close the requested length is to
    // overflow, and test in relation to how much the length will increase.
    val topLo = ((lmaskLor & len).asUInt + (lmaskLor & base).asUInt) // .resize(capAddrPlus2)
    val mwLsbMask = (lmaskLor ^ lmaskLo)
    // If the first bit of the mantissa of the top is not the sum of the
    // corrosponding bits of base and length, there was a carry in.
    val lengthCarryIn = (mwLsbMask & top) =/= ((mwLsbMask & base) ^ (mwLsbMask & len));
    val lengthRoundUp = lostSignificantTop;
    val lengthIsMax = (len & (~lmaskLor)) === (lmask ^ lmaskLor);
    val lengthIsMaxLessOne = (len & (~lmaskLor)) === (lmask ^ lmaskLo);

    val lengthOverflow = False;
    when(lengthIsMax && (lengthCarryIn || lengthRoundUp)) {
      lengthOverflow := True
    }
    when(lengthIsMaxLessOne && lengthCarryIn && lengthRoundUp) {
      lengthOverflow := True
    }

    val e2 = UInt(e1.getWidth bits)
    val tempTopBits = Bits(mlen bits)
    val tempBaseBits = Bits(mlen bits)
    when(lengthOverflow && intExp) {
      e2 := e1 + 1
      when(lostSignificantTopHigher) {
        tempTopBits := (newTopBitsHigher.asUInt + U"1000").resize(mlen).asBits
      } otherwise {
        tempTopBits := newTopBitsHigher.resize(mlen)
      }
      tempBaseBits := newBaseBits.resizeLeft(mlen)
    } otherwise {
      e2 := e1
      when(lostSignificantTop) {
        tempTopBits := (newTopBits.asUInt + U"1000").resize(mlen).asBits
      } otherwise {
        tempTopBits := newTopBits.resize(mlen)
      }
      tempBaseBits := newBaseBits.resize(mlen)
    }
    val exact = !(lostSignificantBase || lostSignificantTop)

    // ret.bounds.exp = e;
    val retExp = e2
    // Update the addrBits fields
    // ret.addrBits = ret.bounds.baseBits;
    val retAddrBits = tempBaseBits
    // Derive new format from newly computed exponent value, and round top up if
    // necessary
    val isEmbExp = Bool
    val retTopBits = Bits(mlen bits)
    val retBaseBits = Bits(mlen bits)
    when(!intExp) { // If we have an Exp of 0 and no implied MSB of L.
      isEmbExp := False
      retTopBits := tempTopBits
      retBaseBits := tempBaseBits
    } otherwise {
      isEmbExp := True
      val botZeroes = B(0, halfExplen bits)
      retBaseBits := tempBaseBits.resizeLeft(mlen - halfExplen) ## botZeroes;
      retTopBits := tempTopBits.resizeLeft(mlen - halfExplen) ## botZeroes;
    }

    // Begin calculate newLength in case this is a request just for a
    // representable length:
    val newLength = UInt(capAddrPlus2 bits)
    val tmpLength = (B"00" ## inLength).resize(capAddrPlus2).asUInt
    val baseMask = S(-1, capAddrPlus2 bits).asBits // Override the result from the previous line if
    // we represent everything.
    when(intExp) {
      val oneInLsb = (lmask ^ (lmask |>> 1)) |>> shiftAmount
      val newLengthRoundedA = tmpLength + oneInLsb.asUInt
      newLength := (tmpLength & (~lmaskLor.asUInt))
      val newLengthRoundedB = (newLengthRoundedA & (~lmaskLor.asUInt))
      when(lostSignificantLen) {
        newLength := newLengthRoundedB
      }
      when(lengthIsMax && lostSignificantTop) {
        baseMask := ~lmaskLo
      } otherwise {
        baseMask := ~lmaskLor
      }
    } otherwise {
      newLength := tmpLength
    }

    // In parallel, work out if the result is going to be in bounds

    // Base computation simple since tf and addrBits already extracted
    // Logic same as capInBounds
    val newBaseInBounds = Bool
    when(baseHi === addrHi) {
      newBaseInBounds := (this.addrBits.asUInt >= this.baseBits.asUInt)
    } otherwise {
      newBaseInBounds := addrHi
    }

    // Interpret the requested length relative to the authorising cap
    val lengthShifted = inLength |>> this.exp

    // Split the length into the mantissa, and the bits that overflowed
    val lengthExcess = lengthShifted.asBits.resizeLeft(xlen - mlen)
    val lengthBits = lengthShifted.resize(mlen)

    // If length didn't fit into the mantissa, it's definitely too big
    val lengthDisqualified = lengthExcess =/= 0

    // Compute the new top bits, assuming the same exponent
    val reqTopBits = (U(B"0" ## this.addrBits) + U(B"0" ## lengthBits)).asBits.resize(mlen + 1)

    // Find the difference between the current and new top bits
    val topDiff =
      S(U(this.getCorrections._2 ## this.topBits) - U(B"0" ## reqTopBits), (mlen + 2) bits)

    // Compute on bits below the mantissa for edge cases
    val lowMask = ~(~B(0, capAddrPlus2 bits) |<< this.exp)
    val carryMask = ~lowMask & (lowMask |<< 1);

    // Recover carry inputs to each bit of top calculation
    val carries = len ^ base ^ top;

    val lowCarry = (carries & carryMask) =/= 0;
    val lowRemainder = (top & lowMask) =/= 0;

    // Address the cases for the top: difference in the mantissa bits dictates slack in the lower bits
    val newTopInBounds = !lengthDisqualified && (
      topDiff > 1
        || (topDiff === 1 && !(lowCarry && lowRemainder))
        || (topDiff === 0 && !(lowCarry || lowRemainder))
    )

    // Address the last case: address is zero being interpreted as the top of the address space.
    val addressWrap = len === 0 && this.address === 0 && this.baseBits =/= 0;

    val resultInBounds = newBaseInBounds && newTopInBounds && !addressWrap;

    // set return cap
    val retCap = RegCapability()

    retCap.embeddedExp := isEmbExp
    when(isEmbExp) {
      retCap.compressedBase :=
        U(retBaseBits.resizeLeft(mlen - halfExplen) ## retExp.resize(halfExplen))
      retCap.compressedTop :=
        U(retTopBits.resizeLeft(mlen - halfExplen) ## retExp.asBits.resizeLeft(halfExplen))
    } otherwise {
      retCap.compressedBase := U(retBaseBits)
      retCap.compressedTop := U(retTopBits)
    }
    retCap.address := this.address
    retCap.otype := this.otype
    retCap.perms.assignFrom(this.perms)
    retCap.tag := this.tag
    retCap.padding := 0

    (exact, resultInBounds, retCap)
  }
}

object RegCapability {
  def Null(implicit context: Context): RegCapability = {
    val cap = RegCapability().assignNull()
    cap.padding := 0
    cap
  }

  def Root(implicit context: Context): RegCapability = {
    val cap = RegCapability().assignRoot()
    cap.padding := 0
    cap
  }
}

case class MemPermissions()(implicit context: Context) extends Bundle with Permissions {
  private val padding1 = B"0" // reserved: global
  override val execute = Bool()
  override val load = Bool()
  override val store = Bool()
  override val loadCapability = Bool()
  override val storeCapability = Bool()
  private val padding2 = B"0" // reserved: storeLocalCapability
  override val seal = Bool()
  override val cinvoke = Bool()
  override val unseal = Bool()
  override val accessSystemRegisters = Bool()

  private val padding3 = B"0" // reserved: setCID
  if (context.config.xlen == 64) {
    padding3 := B"00000" // + uperm (not implemented)
  }

  if (context.config.xlen == 64) {
    assert(getBitsWidth == 16)
  } else if (context.config.xlen == 32) {
    assert(getBitsWidth == 12)
  }
}

case class MemCapability()(implicit context: Context) extends Bundle with Capability {

  override def xlen = context.config.xlen

  override def mlen: Int = context.mlen

  override def explen: Int = context.expLen

  override val address = UInt(xlen bits)

  val packedBase = Bits(mlen bits)

  val packedTop = Bits(mlen - 2 bits)

  override val embeddedExp = Bool()
  override val otype = ObjectType()

  private val padding1 = B"0" // RISCV cap mode flag (unimplemented)
  override val perms = MemPermissions()

  // private val padding2 = B(0, xlen - perms.getBitsWidth - otype.getBitsWidth - 1 bits) //not required in compressed case
  override val tag = Bool()

  assert(getBitsWidth == context.clen + 1)

  override def compressedBase: UInt = packedBase.asUInt

  override def compressedTop: UInt = {
    // unpack packedTop: derive top 2 bits

    val topBits = Bits(context.mlen - 2 bits)
    val lenCorrection = Bits(2 bits)

    when(embeddedExp === False) {
      topBits := packedTop
      lenCorrection := B"00"
    } otherwise {
      topBits := (packedTop.resizeLeft(halfExplen)) ## B(0, halfExplen bits)
      lenCorrection := B"01"
    }

    val carryOut = Bits(2 bits)
    when(topBits.asUInt < baseBits.resize(context.mlen - 2).asUInt) {
      carryOut := B"01"
    } otherwise {
      carryOut := B"00"
    }

    val impliedTopBits =
      (baseBits.asBits.resizeLeft(2).asUInt + carryOut.asUInt + lenCorrection.asUInt).resize(2)
    return (impliedTopBits ## packedTop).asUInt // we keep the exponent bits in the topBits
  }

  private def nullCapBits: Bits =
    MemCapability().assignFrom(RegCapability.Null).asBits.resize(context.clen)

  def value: UInt = {
    // xor with null_cap bits
    // https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-987.pdf p. 85
    (asBits.resize(context.clen) ^ nullCapBits).asUInt
  }

  def assignValue(value: UInt): Unit = {
    // xor with null_cap bits
    // https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-987.pdf p. 85
    assignFromBits(value.asBits ^ nullCapBits, 0, context.clen bits)
  }

  override def assignFrom(other: Capability): this.type = {
    address := other.address
    embeddedExp := other.embeddedExp
    packedBase := other.compressedBase.asBits
    packedTop := other.compressedTop.resize(mlen - 2 bits).asBits
    perms.assignFrom(other.perms)
    otype := other.otype
    tag := other.tag
    this
  }

  assert(
    getBitsWidth == context.clen + 1,
    s"Bit width of MemCapability is ${getBitsWidth} but should be ${context.clen + 1}"
  )
}
