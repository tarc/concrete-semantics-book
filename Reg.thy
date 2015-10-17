theory Reg imports Main
begin

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp =
  N val |
  V vname |
  Plus aexp aexp


fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |
  "aval (V x) s = s x" |
  "aval (Plus a1 a2) s = aval a1 s + aval a2 s"



type_synonym reg = nat
type_synonym rstate = "reg \<Rightarrow> val"

datatype instr =
  LDI int reg |
  LD vname reg |
  ADD reg reg

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec1 ( LDI i r ) s rs = rs ( r := i )" |
  "exec1 ( LD  x r ) s rs = rs ( r := ( s x ) )" |
  "exec1 ( ADD r1 r2 ) s rs = rs ( r1 := ( rs r1 + rs r2 ) )"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec [] _ rs = rs" |
  "exec ( i # is ) s rs = exec is s ( exec1 i s rs )"



fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
  "comp ( N i ) r = [ LDI i r ]" |
  "comp ( V x ) r = [ LD x r ]" |
  "comp ( Plus a1 a2 ) r =  comp a1 r  @  comp a2 ( r + 1 )  @  [ ADD r ( r + 1 ) ]"

lemma append_compose : "exec ( is1 @ is2 ) s rs = exec is2 s ( exec is1 s rs )"
  apply ( induction is1 arbitrary: is2 s rs)
  apply ( auto )
done

lemma immutable_lesser_states :
  "r2 > r1 \<Longrightarrow> exec ( comp a r2 ) s rs r1 = rs r1"

  apply ( induction a arbitrary: r2 rs )
  apply ( auto simp: append_compose )
done

lemma correctness : "exec ( comp a r ) s rs r = aval a s"
  apply ( induction a arbitrary: r s rs )
  apply ( auto simp: append_compose immutable_lesser_states )
done

end