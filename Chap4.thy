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

lemma doublT : "T w \<Longrightarrow> T v \<Longrightarrow> T ( w @ v)"
  apply ( induction rule: T.induct )
  apply ( auto )

lemma "S w \<Longrightarrow> T w"
  apply ( induction rule: S.induct )
  apply ( rule emptyT )
  apply ( rule app_emp )
  apply ( rule alter )
  apply ( rule emptyT )
  apply ( assumption )

end