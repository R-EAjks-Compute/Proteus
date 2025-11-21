package riscv.plugins.memory

import spinal.core.HardType
import spinal.core.Data
import spinal.core.Component
import riscv.MemBus

trait MetadataProvider {
  def getKey: Metadata
  def getHardType: HardType[Data]
  def build(bus: MemBus): Component
}

trait Metadata {
  def name: String = getClass.getSimpleName.takeWhile(_ != '$')

  override def toString: String = name
}
