package examples

import chisel3._

/**
 * Base module for all designs to ensure consistent FIRRTL annotations.
 */
abstract class BaseModule extends Module {
  // Intentionally minimal; shared FIRRTL annotations can be added here when available
}
