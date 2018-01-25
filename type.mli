(* Through a CPS transformation, the surface language [Lambda] is translated
   down to the intermediate language [Tail]. *)

val type_term: Lambda.term -> Lambda.term
