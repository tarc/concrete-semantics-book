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
  LDI val reg |
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



datatype instr0 =
  LDI0 int |
  LD0 vname |
  MV0 reg |
  ADD0 reg

fun exec01 :: "instr0 \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec01 ( LDI0 i ) s rs = rs ( 0 := i )" |
  "exec01 ( LD0  x ) s rs = rs ( 0 := ( s x ) )" |
  "exec01 ( MV0 r ) s rs = rs ( r := ( rs 0 ) )" |
  "exec01 ( ADD0 r ) s rs = rs ( 0 := ( rs 0 + rs r ) )"

fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec0 [] _ rs = rs" |
  "exec0 ( i # is ) s rs = exec0 is s ( exec01 i s rs )"



fun comp0 :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
  "comp0 ( N i ) r = [ LDI0 i , MV0 r ]" |
  "comp0 ( V x ) r = [ LD0 x , MV0 r ]" |
  "comp0 ( Plus a1 a2 ) r = comp0 a1 ( r + 1 ) @  comp0 a2 ( r + 2 )  @
                            [ LDI0 0 , ADD0 ( r + 1 ) , ADD0 ( r + 2 ) , MV0 r ]"

lemma exec0_append_compose : "exec0 ( is1 @ is2 ) s rs = exec0 is2 s ( exec0 is1 s rs )"
  apply ( induction is1 arbitrary: rs )
  apply ( auto )
done

lemma exec0_immutable_lesser_states :
  "( r2 > r1 \<and> r1 > 0 ) \<Longrightarrow> exec0 ( comp0 a r2 ) s rs r1 = rs r1"

  apply ( induction a arbitrary: r2 rs )
  apply ( auto simp: exec0_append_compose )
done

lemma "exec0 ( comp0 a r ) s rs r = exec0 ( comp0 a r ) s rs 0"
  apply ( induction a r rule: comp0.induct )
  apply ( auto simp: exec0_append_compose)
done

lemma exec0_correctness : "exec0 ( comp0 a r ) s rs r = aval a s"
  apply ( induction a arbitrary: r s rs )
  apply ( auto simp: exec0_append_compose exec0_immutable_lesser_states )
done

end