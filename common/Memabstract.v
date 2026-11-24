Require Import Coqlib AST Values Memdata Memtype.

Module Type ABSTRACT_MEM.

Parameter mem: Type.

Parameter valid_pointer: mem -> block -> Z -> bool.

Parameter loadv: memory_chunk -> mem -> val -> option val.
Parameter storev: memory_chunk -> mem -> val -> val -> option mem.

End ABSTRACT_MEM.