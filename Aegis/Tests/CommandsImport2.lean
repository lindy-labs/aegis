import Aegis.Tests.CommandsImport
import Aegis.Tests.Commands

/--
info: Starting pc: 0
Input types: [core::bool, core::bool]
Output types: [core::bool] -/
#guard_msgs in
aegis_info "test::bar"

aegis_complete
