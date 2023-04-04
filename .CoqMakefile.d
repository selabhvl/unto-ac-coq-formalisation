acomputing/syntax.vo acomputing/syntax.glob acomputing/syntax.v.beautified acomputing/syntax.required_vo: acomputing/syntax.v 
acomputing/syntax.vio: acomputing/syntax.v 
acomputing/syntax.vos acomputing/syntax.vok acomputing/syntax.required_vos: acomputing/syntax.v 
lib/basics.vo lib/basics.glob lib/basics.v.beautified lib/basics.required_vo: lib/basics.v acomputing/syntax.vo lib/nvalues.vo
lib/basics.vio: lib/basics.v acomputing/syntax.vio lib/nvalues.vio
lib/basics.vos lib/basics.vok lib/basics.required_vos: lib/basics.v acomputing/syntax.vos lib/nvalues.vos
lib/nvalues.vo lib/nvalues.glob lib/nvalues.v.beautified lib/nvalues.required_vo: lib/nvalues.v acomputing/syntax.vo
lib/nvalues.vio: lib/nvalues.v acomputing/syntax.vio
lib/nvalues.vos lib/nvalues.vok lib/nvalues.required_vos: lib/nvalues.v acomputing/syntax.vos
lib/value_tree.vo lib/value_tree.glob lib/value_tree.v.beautified lib/value_tree.required_vo: lib/value_tree.v acomputing/syntax.vo
lib/value_tree.vio: lib/value_tree.v acomputing/syntax.vio
lib/value_tree.vos lib/value_tree.vok lib/value_tree.required_vos: lib/value_tree.v acomputing/syntax.vos
lib/sensor_state.vo lib/sensor_state.glob lib/sensor_state.v.beautified lib/sensor_state.required_vo: lib/sensor_state.v acomputing/syntax.vo
lib/sensor_state.vio: lib/sensor_state.v acomputing/syntax.vio
lib/sensor_state.vos lib/sensor_state.vok lib/sensor_state.required_vos: lib/sensor_state.v acomputing/syntax.vos
acomputing/big_step_semantics.vo acomputing/big_step_semantics.glob acomputing/big_step_semantics.v.beautified acomputing/big_step_semantics.required_vo: acomputing/big_step_semantics.v acomputing/syntax.vo lib/basics.vo lib/sensor_state.vo lib/value_tree.vo lib/nvalues.vo
acomputing/big_step_semantics.vio: acomputing/big_step_semantics.v acomputing/syntax.vio lib/basics.vio lib/sensor_state.vio lib/value_tree.vio lib/nvalues.vio
acomputing/big_step_semantics.vos acomputing/big_step_semantics.vok acomputing/big_step_semantics.required_vos: acomputing/big_step_semantics.v acomputing/syntax.vos lib/basics.vos lib/sensor_state.vos lib/value_tree.vos lib/nvalues.vos
test/basics_test.vo test/basics_test.glob test/basics_test.v.beautified test/basics_test.required_vo: test/basics_test.v lib/basics.vo lib/nvalues.vo acomputing/syntax.vo
test/basics_test.vio: test/basics_test.v lib/basics.vio lib/nvalues.vio acomputing/syntax.vio
test/basics_test.vos test/basics_test.vok test/basics_test.required_vos: test/basics_test.v lib/basics.vos lib/nvalues.vos acomputing/syntax.vos
test/nvalues_test.vo test/nvalues_test.glob test/nvalues_test.v.beautified test/nvalues_test.required_vo: test/nvalues_test.v acomputing/syntax.vo lib/nvalues.vo
test/nvalues_test.vio: test/nvalues_test.v acomputing/syntax.vio lib/nvalues.vio
test/nvalues_test.vos test/nvalues_test.vok test/nvalues_test.required_vos: test/nvalues_test.v acomputing/syntax.vos lib/nvalues.vos
test/value_tree_test.vo test/value_tree_test.glob test/value_tree_test.v.beautified test/value_tree_test.required_vo: test/value_tree_test.v acomputing/syntax.vo lib/nvalues.vo lib/value_tree.vo
test/value_tree_test.vio: test/value_tree_test.v acomputing/syntax.vio lib/nvalues.vio lib/value_tree.vio
test/value_tree_test.vos test/value_tree_test.vok test/value_tree_test.required_vos: test/value_tree_test.v acomputing/syntax.vos lib/nvalues.vos lib/value_tree.vos
test/sensor_state_test.vo test/sensor_state_test.glob test/sensor_state_test.v.beautified test/sensor_state_test.required_vo: test/sensor_state_test.v lib/sensor_state.vo acomputing/syntax.vo
test/sensor_state_test.vio: test/sensor_state_test.v lib/sensor_state.vio acomputing/syntax.vio
test/sensor_state_test.vos test/sensor_state_test.vok test/sensor_state_test.required_vos: test/sensor_state_test.v lib/sensor_state.vos acomputing/syntax.vos
