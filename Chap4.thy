theory Chap4 imports Main
begin


datatype 'a tree =
  Tip |
  Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
  "set Tip = {}" |
  "set ( Node lt r rt ) = { r } \<union> ( set lt ) \<union> ( set rt )"

fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True" |
  "ord ( Node lt r rt ) = (
                            ( ord lt ) \<and>
                            ( ord rt ) \<and>
                            ( \<forall> x \<in> ( set lt ) . x < r ) \<and>
                            ( \<forall> x \<in> ( set rt ) . r < x ) )"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
  "ins x Tip = ( Node Tip x Tip )" |
  "ins x ( Node lt r rt ) =
    ( if x = r then
      ( Node lt r rt ) else
      ( if x < r then
        (Node ( ins x lt ) r rt ) else
        (Node lt r ( ins x rt ) ) ) )"

lemma ins_union : "set ( ins x t ) = { x } \<union> set t"
  apply ( induction t )
  apply ( auto )
done

lemma "ord t \<Longrightarrow> ord ( ins i t )"
  apply ( induction t )
  apply ( auto simp: ins_union )
done

thm Suc_leD

lemma "Suc ( Suc ( Suc a ) ) \<le> b \<Longrightarrow> a \<le> b"
  apply ( rule Suc_leD )
  apply ( rule Suc_leD )
  apply ( rule Suc_leD )
  apply ( blast )
done


inductive ev :: "nat \<Rightarrow> bool" where
  ev0 :   "ev 0" |
  evSS:   "ev n \<Longrightarrow> ev ( Suc ( Suc n ) )"


lemma "ev ( Suc ( Suc ( Suc ( Suc 0 ) ) ) )"
  apply ( rule evSS )
  apply ( rule evSS )
  apply ( rule ev0 )
done

fun evn :: "nat \<Rightarrow> bool" where
  "evn 0 = True" |
  "evn ( Suc 0 ) = False" |
  "evn ( Suc ( Suc n ) ) = evn n"



lemma "ev m \<Longrightarrow> evn m"
  apply ( induction rule: ev.induct )
  apply ( simp_all )
done

lemma "evn m \<Longrightarrow> ev m"
  apply ( induction rule: evn.induct )
  apply ( rule ev0 )
  apply ( simp )
  apply ( simp )
  apply ( rule evSS )
  apply ( blast )
done


inductive star :: "( 'a \<Rightarrow> 'a \<Rightarrow> bool ) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl  : "star r x x" |
  step  : "r x y  \<Longrightarrow>  star r y z  \<Longrightarrow>  star r x z"

value "(star r y z' \<Longrightarrow> star r x z')"
thm star.induct [where ?P="\<lambda> x y . (star r y z' \<longrightarrow> star r x z')" and ?r="r" and ?x1.0="x" and ?x2.0="y"]


lemma star_trans : "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply ( induction rule: star.induct )
  apply ( assumption )
  apply ( metis step )
done

lemma rev_star : "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply ( induction rule: star.induct )
  apply ( rule step )
  apply ( simp_all  add: step refl)
  apply ( rule refl )
done

inductive palindrome :: "'a list \<Rightarrow> bool" where
  empty : "palindrome []" |
  singl : "palindrome [x]" |
  sandw : "palindrome xs  \<Longrightarrow>  palindrome ( a # xs @ [a] )"

lemma "palindrome xs  \<Longrightarrow>  rev xs = xs"
  apply ( induction rule: palindrome.induct )
  apply ( simp_all )
done



inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl' : "star' r x x" |
  step' : "star' r x y  \<Longrightarrow>  r y z  \<Longrightarrow>  star' r x z"


lemma "star' r x y \<Longrightarrow> star r x y"
  apply ( induction rule: star'.induct )
  apply ( rule refl )
  apply ( simp add: rev_star )
done


lemma rev_star' : "star' r y z  \<Longrightarrow>  r x y  \<Longrightarrow>  star' r x z"
  apply ( induction rule: star'.induct )
  apply ( rule step' [of "r" "x" "x"] )
  apply ( rule refl' )
  apply ( assumption )
  apply ( metis step')
done


lemma "star r x y \<Longrightarrow> star' r x y"
  apply ( induction rule: star.induct )
  apply ( rule refl' )
  apply ( metis rev_star' )
done


inductive iter :: "( 'a \<Rightarrow> 'a \<Rightarrow> bool ) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl_i : "iter r 0 x x" |
  step_i : "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r ( n + 1 ) x z"

lemma "star r x y \<Longrightarrow> \<exists> n . iter r n x y"
  apply ( induction rule: star.induct )
  apply ( metis refl_i )
  apply ( metis step_i )
done


datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
  emptyS  : "S []" |
  middl   : "S w \<Longrightarrow> S ( a # w @ [b] )" |
  doubl   : "S w \<Longrightarrow> S v \<Longrightarrow> S ( w @ v )"

inductive T :: "alpha list \<Rightarrow> bool" where
  emptyT  : "T []" |
  alter   : "T w \<Longrightarrow> T v \<Longrightarrow> T ( w @ a # v @ [b] )"



lemma "T w \<Longrightarrow> S w"
  apply ( induction rule: T.induct )
  apply ( rule emptyS )
  apply ( rule doubl )
  apply ( assumption )
  apply ( rule middl )
  apply ( assumption )
done

lemma app_emp : "T ([] @ a # w @ [b]) \<Longrightarrow> T ( a # w @ [b])"
  apply ( auto )
done

lemma assoc_arb : "X ((w @ a # v @ b # wa) @ a # va @ [b]) \<Longrightarrow> X (w @ a # v @ b # wa @ a # va @ [b])"
  apply ( auto )
done


lemma append_T : "T ts \<Longrightarrow> T v \<Longrightarrow> T w \<Longrightarrow> T (w @ a # v @ b # ts)"
  apply ( induction rule: T.induct )
  apply ( metis alter )
  apply ( rule assoc_arb )
  apply ( metis alter )
done

lemma doublT : "T w \<Longrightarrow> T v \<Longrightarrow> T ( w @ v)"
  apply ( induction rule: T.induct )
  apply ( auto )
  apply ( metis append_T )
done

lemma "S w \<Longrightarrow> T w"
  apply ( induction rule: S.induct )
  apply ( rule emptyT )
  apply ( rule app_emp )
  apply ( rule alter )
  apply ( rule emptyT )
  apply ( assumption )
  apply ( metis doublT )
done




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

inductive aval_r :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
  arn : "aval_r ( N n ) s n" |
  arv : "aval_r ( V x ) s ( s x )" |
  arp : "aval_r a1 s v1 \<Longrightarrow> aval_r a2 s v2 \<Longrightarrow> aval_r ( Plus a1 a2 ) s ( v1 + v2)"

lemma "aval_r a0 s v \<Longrightarrow> ( aval a0 s = v )"
  apply ( induction rule: aval_r.induct )
  apply ( auto )
done

lemma aval_r_aval : "aval_r a0 s ( aval a0 s )"
  apply ( induction a0 s rule: aval.induct )
  apply ( auto )
  apply ( metis arn )
  apply ( metis arv )
  apply ( metis arp )
done

lemma "aval a0 s = v \<Longrightarrow> aval_r a0 s v"
  apply ( induction a0 s rule: aval.induct )
  apply ( auto )
  apply ( metis arn )
  apply ( metis arv )
  apply ( rule arp )
  apply ( rule aval_r_aval )
  apply ( rule aval_r_aval )
done





datatype instr =
  LOADI val |
  LOAD vname |
  ADD

type_synonym stack = "val list"

abbreviation "hd2 xs \<equiv> hd ( tl xs )"
abbreviation "tl2 xs \<equiv> tl ( tl xs )"


fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
  "exec1 ( LOADI n ) _ stk = n # stk" |
  "exec1 ( LOAD x ) s stk = ( s x ) # stk" |
  "exec1 ( ADD ) _ stk = ( hd2 stk + hd stk ) # tl2 stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
  "exec [] _ stk = stk" |
  "exec ( i # is ) s stk = exec is s ( exec1 i s stk )"


lemma exec_append : "exec ( is1 @ is2 ) s stk = exec is2 s ( exec is1 s stk )"
  apply ( induction is1 s stk rule: exec.induct )
  apply ( auto )
done

inductive ok1 :: "nat \<Rightarrow> instr \<Rightarrow> nat \<Rightarrow> bool" for n where
  ok1LOADI : "ok1 n ( LOADI c ) ( n + 1 )" |
  ok1LOAD  : "ok1 n ( LOAD x ) ( n + 1 )" |
  ok1ADD   : "n\<ge>2 \<Longrightarrow> ok1 n ADD ( n - 1 )"

lemma ok1_correct :
    "ok1 n i n' \<Longrightarrow> length stk = n \<Longrightarrow> length ( exec1 i s stk ) = n'"
  apply ( induction rule: ok1.induct )
  apply ( simp_all )
done


inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
  ok_refl : "ok n [] n" |
  ok_step : "ok1 n i n1  \<Longrightarrow>  ok n1 is n2  \<Longrightarrow>  ok n ( i # is ) n2"


lemma ok_correct : "ok n is n' \<Longrightarrow> length stk = n \<Longrightarrow> length ( exec is s stk ) = n'"
  apply ( induction arbitrary: stk rule: ok.induct )
  apply ( auto )
  apply ( metis ok1_correct )
done


fun comp :: "aexp \<Rightarrow> instr list" where
  "comp ( aexp.N n ) = [ LOADI n ]" |
  "comp ( aexp.V x ) = [ LOAD x ]" |
  "comp ( aexp.Plus e1 e2 ) = comp e1 @ comp e2 @ [ ADD ]"


lemma exec_comp_inc : "length ( exec ( comp a0 ) s stk ) = length stk + 1"
  apply ( induction a0 arbitrary: stk rule: comp.induct )
  apply ( auto simp add: exec_append )
done


lemma "ok 0 [LOAD x] (Suc 0)"
  apply ( rule )
  apply ( rule )
  apply ( simp )
  apply ( rule )
done

lemma lliadd : "ok 0 [LOAD x, LOADI v, ADD] (Suc 0)"
  apply ( rule )
  apply ( rule )
  apply ( rule )
  apply ( rule )
  apply ( simp )
  apply ( rule )
  apply ( rule )
  apply ( simp )
  apply ( simp )
  apply ( rule )
done

lemma liladd : "ok 0 [LOADI x, LOAD v, ADD] (Suc 0)"
  apply ( rule )
  apply ( rule )
  apply ( rule )
  apply ( rule )
  apply ( simp )
  apply ( rule )
  apply ( rule )
  apply ( simp )
  apply ( simp )
  apply ( rule )
done

lemma liliadd : "ok 0 [LOADI x, LOADI v, ADD] (Suc 0)"
  apply ( rule )
  apply ( rule )
  apply ( rule )
  apply ( rule )
  apply ( simp )
  apply ( rule )
  apply ( rule )
  apply ( simp )
  apply ( simp )
  apply ( rule )
done

lemma "ok (Suc (Suc 0)) [LOAD x, ADD, ADD, LOAD y] (Suc (Suc 0))"
  apply ( rule )
  apply ( rule )
  apply ( rule )
  apply ( rule )
  apply ( simp )
  apply ( rule )
  apply ( simp )
  apply ( rule )
  apply ( simp )
  apply ( rule )
  apply ( simp )
  apply ( rule )
  apply ( simp )
  apply ( rule )
done


fun stackn :: "nat \<Rightarrow> stack" where
  "stackn 0 = []" |
  "stackn ( Suc n ) = 0 # ( stackn n )"

lemma len_stackn : "length ( stackn n ) = n"
  apply ( induction n )
  apply ( auto )
done

lemma ok_append : "ok n1 is1 n2 \<Longrightarrow> ok n2 is2 n3 \<Longrightarrow> ok n1 (is1 @ is2) n3"
  apply ( induction arbitrary: is2 n3 rule: ok.induct )
  apply ( simp_all )
  apply ( rule )
  apply ( auto )
done

lemma ok_comp_add : "
       ( \<And>n . ok n ( comp e1 ) ( Suc n ) ) \<Longrightarrow>
       ( \<And>n . ok n ( comp e2 ) ( Suc n ) ) \<Longrightarrow>
            ok n (comp e1 @ comp e2 @ [ADD]) (Suc n)"

  apply ( rule ok_append )
  apply ( auto )
  apply ( rule ok_append )
  apply ( auto )
  apply ( rule )
  apply ( simp add: ok1.simps )
  apply ( rule )
done

lemma ok_comp_suc : "ok n ( comp a0 ) ( Suc n )"
  apply ( induction a0 arbitrary:n rule: comp.induct )
  apply ( simp add: ok_refl ok_step ok1.simps )
  apply ( simp add: ok_refl ok_step ok1.simps )
  apply ( simp )
  apply ( metis ok_comp_add )
done


lemma "ok n ( comp a0 ) ( length ( exec ( comp a0 ) s (stackn n) ) )"
  apply ( induction a0 arbitrary:n rule: comp.induct )
  apply ( auto simp add: ok1.simps ok_refl ok_step len_stackn exec_comp_inc exec_append)
  apply ( metis ok_comp_add )
done

end