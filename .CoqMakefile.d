xc/syntax.vo xc/syntax.glob xc/syntax.v.beautified xc/syntax.required_vo: xc/syntax.v 
xc/syntax.vio: xc/syntax.v 
xc/syntax.vos xc/syntax.vok xc/syntax.required_vos: xc/syntax.v 
lib/basics.vo lib/basics.glob lib/basics.v.beautified lib/basics.required_vo: lib/basics.v xc/syntax.vo lib/nvalues.vo
lib/basics.vio: lib/basics.v xc/syntax.vio lib/nvalues.vio
lib/basics.vos lib/basics.vok lib/basics.required_vos: lib/basics.v xc/syntax.vos lib/nvalues.vos
lib/nvalues.vo lib/nvalues.glob lib/nvalues.v.beautified lib/nvalues.required_vo: lib/nvalues.v xc/syntax.vo
lib/nvalues.vio: lib/nvalues.v xc/syntax.vio
lib/nvalues.vos lib/nvalues.vok lib/nvalues.required_vos: lib/nvalues.v xc/syntax.vos
lib/value_tree.vo lib/value_tree.glob lib/value_tree.v.beautified lib/value_tree.required_vo: lib/value_tree.v xc/syntax.vo lib/nvalues.vo
lib/value_tree.vio: lib/value_tree.v xc/syntax.vio lib/nvalues.vio
lib/value_tree.vos lib/value_tree.vok lib/value_tree.required_vos: lib/value_tree.v xc/syntax.vos lib/nvalues.vos
lib/sensor_state.vo lib/sensor_state.glob lib/sensor_state.v.beautified lib/sensor_state.required_vo: lib/sensor_state.v xc/syntax.vo
lib/sensor_state.vio: lib/sensor_state.v xc/syntax.vio
lib/sensor_state.vos lib/sensor_state.vok lib/sensor_state.required_vos: lib/sensor_state.v xc/syntax.vos
xc/big_step_semantics.vo xc/big_step_semantics.glob xc/big_step_semantics.v.beautified xc/big_step_semantics.required_vo: xc/big_step_semantics.v xc/syntax.vo lib/basics.vo lib/sensor_state.vo lib/value_tree.vo lib/nvalues.vo
xc/big_step_semantics.vio: xc/big_step_semantics.v xc/syntax.vio lib/basics.vio lib/sensor_state.vio lib/value_tree.vio lib/nvalues.vio
xc/big_step_semantics.vos xc/big_step_semantics.vok xc/big_step_semantics.required_vos: xc/big_step_semantics.v xc/syntax.vos lib/basics.vos lib/sensor_state.vos lib/value_tree.vos lib/nvalues.vos
xc/network_semantics.vo xc/network_semantics.glob xc/network_semantics.v.beautified xc/network_semantics.required_vo: xc/network_semantics.v xc/syntax.vo lib/basics.vo lib/sensor_state.vo lib/value_tree.vo lib/nvalues.vo xc/big_step_semantics.vo
xc/network_semantics.vio: xc/network_semantics.v xc/syntax.vio lib/basics.vio lib/sensor_state.vio lib/value_tree.vio lib/nvalues.vio xc/big_step_semantics.vio
xc/network_semantics.vos xc/network_semantics.vok xc/network_semantics.required_vos: xc/network_semantics.v xc/syntax.vos lib/basics.vos lib/sensor_state.vos lib/value_tree.vos lib/nvalues.vos xc/big_step_semantics.vos
xc/tactics.vo xc/tactics.glob xc/tactics.v.beautified xc/tactics.required_vo: xc/tactics.v xc/syntax.vo lib/basics.vo lib/sensor_state.vo lib/value_tree.vo lib/nvalues.vo xc/big_step_semantics.vo
xc/tactics.vio: xc/tactics.v xc/syntax.vio lib/basics.vio lib/sensor_state.vio lib/value_tree.vio lib/nvalues.vio xc/big_step_semantics.vio
xc/tactics.vos xc/tactics.vok xc/tactics.required_vos: xc/tactics.v xc/syntax.vos lib/basics.vos lib/sensor_state.vos lib/value_tree.vos lib/nvalues.vos xc/big_step_semantics.vos
test/basics_test.vo test/basics_test.glob test/basics_test.v.beautified test/basics_test.required_vo: test/basics_test.v lib/basics.vo lib/nvalues.vo xc/syntax.vo
test/basics_test.vio: test/basics_test.v lib/basics.vio lib/nvalues.vio xc/syntax.vio
test/basics_test.vos test/basics_test.vok test/basics_test.required_vos: test/basics_test.v lib/basics.vos lib/nvalues.vos xc/syntax.vos
test/nvalues_test.vo test/nvalues_test.glob test/nvalues_test.v.beautified test/nvalues_test.required_vo: test/nvalues_test.v xc/syntax.vo lib/nvalues.vo lib/value_tree.vo
test/nvalues_test.vio: test/nvalues_test.v xc/syntax.vio lib/nvalues.vio lib/value_tree.vio
test/nvalues_test.vos test/nvalues_test.vok test/nvalues_test.required_vos: test/nvalues_test.v xc/syntax.vos lib/nvalues.vos lib/value_tree.vos
test/value_tree_test.vo test/value_tree_test.glob test/value_tree_test.v.beautified test/value_tree_test.required_vo: test/value_tree_test.v xc/syntax.vo lib/nvalues.vo lib/value_tree.vo
test/value_tree_test.vio: test/value_tree_test.v xc/syntax.vio lib/nvalues.vio lib/value_tree.vio
test/value_tree_test.vos test/value_tree_test.vok test/value_tree_test.required_vos: test/value_tree_test.v xc/syntax.vos lib/nvalues.vos lib/value_tree.vos
test/sensor_state_test.vo test/sensor_state_test.glob test/sensor_state_test.v.beautified test/sensor_state_test.required_vo: test/sensor_state_test.v lib/sensor_state.vo xc/syntax.vo
test/sensor_state_test.vio: test/sensor_state_test.v lib/sensor_state.vio xc/syntax.vio
test/sensor_state_test.vos test/sensor_state_test.vok test/sensor_state_test.required_vos: test/sensor_state_test.v lib/sensor_state.vos xc/syntax.vos
