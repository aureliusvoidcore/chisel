#include <ebmc/property_checker.h>
#include <ebmc/ic3_engine.h>
#include <util/message.h>

// Stubs for features not currently available in the WebAssembly build.

property_checker_resultt ic3_engine(
  const cmdlinet &cmdline,
  transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  message.warning() << "IC3 engine is not available in the WebAssembly build; use BMC or k-induction options instead." << messaget::eom;
  // Mark unsupported properties with failure to be explicit
  for(auto &prop : properties.properties) {
    if(!prop.is_disabled()) {
      prop.failure("IC3 engine not available in WebAssembly build");
    }
  }
  return property_checker_resultt{properties};
}
