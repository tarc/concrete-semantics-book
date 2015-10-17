theory ASM imports Main begin



type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp =
  N val |
  V vname |
  Plus aexp aexp



definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"

value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"



fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |
  "aval (V x) s = s x" |
  "aval (Plus a1 a2) s = aval a1 s + aval a2 s"





datatype instr =
  LOADI val |
  LOAD vname |
  ADD

type_synonym stack = "val list"

abbreviation "hd2 xs \<equiv> hd ( tl xs )"
abbreviation "tl2 xs \<equiv> tl ( tl xs )"



fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
  "exec1 ( LOADI n ) _ stk = Some ( n # stk )" |
  "exec1 ( LOAD x ) s stk = Some ( ( s x ) # stk )" |
  "exec1 ADD _ [] = None" |
  "exec1 ADD _ [ h ] = None" |
  "exec1 ADD _ ( h1 # ( h2 # hs ) ) = Some ( ( h2 + h1 ) # hs )"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
  "exec [] _ stk = Some stk" |
  "exec ( i # is ) s stk =
    ( case ( exec1 i s stk ) of
      ( Some stk' ) \<Rightarrow> ( exec is s stk' ) |
           None     \<Rightarrow>       None )"



fun comp :: "aexp \<Rightarrow> instr list" where
  "comp ( aexp.N n ) = [ LOADI n ]" |
  "comp ( aexp.V x ) = [ LOAD x ]" |
  "comp ( aexp.Plus e1 e2 ) = comp e1 @ comp e2 @ [ ADD ]"



end
