package riscv.plugins.cheri

import riscv._

case class Context(pipeline: Pipeline)(implicit val config: Config) {
  val clen = 2 * config.xlen // capability length

  val otypeLen = if (config.xlen == 32) { 4 }
  else { 18 } // bit width reserved for the Object Type field
  val maxOtype =
    (1 << otypeLen) - 4 // value used to know whether a capability is sealed, cf https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-951.pdf p. 78

  // val UPermLen = if(config.xlen == 32){ 0 } else { 4 }; //for now unused
  val mlen = if (config.xlen == 32) { 8 }
  else { 14 };
  val expLen = if (config.xlen == 32) { 6 }
  else { 6 };
  val flagsLen = 1; // for RISCV

  val data = new GlobalPipelineData(pipeline)(this)
}
