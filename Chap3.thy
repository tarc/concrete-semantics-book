theory Chap3
imports Main
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


fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const ( N n ) = N n" |
  "asimp_const ( V x ) = V x" |
  "asimp_const ( Plus a1 a2 ) =
    ( case ( asimp_const a1 , asimp_const a2 ) of
        ( N n1 , N n2 ) \<Rightarrow> N ( n1 + n2 ) |
        ( b1 , b2 ) \<Rightarrow> Plus b1 b2 )"

lemma "aval ( asimp_const a ) s = aval a s"
  apply ( induction a )
  apply ( auto  split: aexp.split )
done


fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus ( N i1 ) ( N i2 ) = N ( i1 + i2 )"|
  "plus ( N i ) a = ( if  i = 0  then  a  else (  Plus ( N i ) a  ) )" |
  "plus a ( N i ) = ( if  i = 0  then  a  else (  Plus a ( N i )  ) )" |
  "plus a1 a2 = Plus a1 a2"

lemma aval_plus : "aval ( plus a1 a2 ) s = aval a1 s + aval a2 s"
  apply ( induction rule: plus.induct )
  apply ( auto )
done


fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp ( N n ) = N n" |
  "asimp ( V x ) = V x" |
  "asimp ( Plus a1 a2 ) = plus ( asimp a1 ) ( asimp a2 )"

lemma "assimp_correct" : "aval ( asimp a ) s = aval a s"
  apply ( induction a )
  apply ( auto simp add: aval_plus )
done



fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal ( N n ) = True" |
  "optimal ( V x ) = True" |
  "optimal ( Plus ( N i ) ( N j ) ) = False" |
  "optimal ( Plus a1 a2 ) = ( optimal a1 \<and>  optimal a2 )"

lemma "optimal ( asimp_const a )"
  apply ( induction a )
  apply ( auto split: aexp.split)
done





fun full_asimp :: "aexp \<Rightarrow> aexp" where
  "full_asimp ( N n ) = N n" |
  "full_asimp ( V x ) = V x" |
  "full_asimp ( Plus a1 a2 ) =
    ( case ( full_asimp a1 , full_asimp a2 ) of
      ( N n1              , N n2 )              \<Rightarrow> ( N ( n1 + n2 ) ) |
      ( N n               , V y  )              \<Rightarrow> ( Plus ( V y ) ( N n ) ) |
      ( N n1              , Plus a2' ( N n2 ) ) \<Rightarrow> ( Plus a2' (N  (n1 + n2)) ) |
      ( N n               , Plus a21 a22 )      \<Rightarrow> ( Plus ( Plus a21 a22 ) ( N n ) ) |
      ( V x               , N n  )              \<Rightarrow> ( Plus ( V x ) ( N n ) ) |
      ( V x               , V y  )              \<Rightarrow> ( Plus ( V x ) ( V y ) ) |
      ( V x               , Plus a2' ( N n2 ) ) \<Rightarrow> ( Plus ( Plus ( V x ) a2' ) ( N  n2 ) ) |
      ( V x               , Plus a21 a22 )      \<Rightarrow> ( Plus ( V x ) ( Plus a21 a22 ) ) |
      ( Plus a1' ( N n1 ) , N n2 )              \<Rightarrow> ( Plus a1' ( N ( n1 + n2 ) ) ) |
      ( Plus a1' ( N n )  , V x  )              \<Rightarrow> ( Plus ( Plus a1' ( V x ) ) ( N n ) ) |
      ( Plus a1' ( N n1 ) , Plus a2' ( N n2 ) ) \<Rightarrow> ( Plus ( Plus a1' a2' ) (N  (n1 + n2)) ) |
      ( Plus a1' ( N n )  , Plus a21 a22)       \<Rightarrow> ( Plus ( Plus a1' ( Plus a21 a22 ) ) ( N n ) ) |
      ( Plus a11 a12      , N n  )              \<Rightarrow> ( Plus ( Plus a11 a12 ) ( N n ) ) |
      ( Plus a11 a12      , V x  )              \<Rightarrow> ( Plus ( Plus a11 a12 ) ( V x ) ) |
      ( Plus a11 a12      , Plus a2' ( N n ) )  \<Rightarrow> ( Plus ( Plus a11 ( Plus  a12 a2' ) ) ( N n ) ) |
      ( Plus a11 a12      , Plus a21 a22 )      \<Rightarrow> ( Plus ( Plus a11 a12 ) ( Plus a21 a22 ) ) )"

lemma "aval ( full_asimp a ) s = aval a s"
  apply ( induction a )
  apply ( auto split: aexp.split)
done



fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst _ _ ( N n ) = N n" |
  "subst x t ( V y ) = ( if x = y then t else V y )" |
  "subst x t ( Plus a1 a2 ) = Plus ( subst x t  a1 ) ( subst x t a2 )"

lemma "substitution_lemma" : "aval ( subst x t e ) s = aval e ( s ( x := aval t s ) )"
  apply ( induction e )
  apply ( auto )
done

lemma "subst_equiv" : "aval a1 s = aval a2 s \<Longrightarrow> aval ( subst x a1 e ) s = aval ( subst x a2 e ) s"
  apply ( simp add: substitution_lemma )
done



datatype aexp2 =
  N val |
  V vname |
  Inc vname |
  Plus aexp2 aexp2 |
  Div aexp2 aexp2


fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> ( val \<times> state ) option" where
  "aval2 ( N i ) s = Some (  i  , s )" |
  "aval2 ( V x ) s = Some ( s x , s )" |
  "aval2 ( Inc x ) s = Some ( s x , s ( x := ( s x ) + 1 ) )" |
  "aval2 ( Plus a1 a2 ) s =
    ( case ( aval2 a1 s ) of
      None \<Rightarrow> None |
      Some ( v1 , s1 ) \<Rightarrow>
        ( case ( aval2 a2 s1 ) of
          None \<Rightarrow> None |
          Some ( v2 , s2 ) \<Rightarrow> Some ( v1 + v2 , s2 ) ) )" |
  "aval2 ( Div a1 a2 ) s =
    ( case ( aval2 a2 s ) of
      None \<Rightarrow> None |
      Some ( v1 , s1 ) \<Rightarrow> ( if v1 = 0 then None else
        ( case ( aval2 a1 s1 ) of
          None \<Rightarrow> None |
          Some ( v2 , s2 ) \<Rightarrow> Some ( v1 div v2 , s2 ) ) ) )"



datatype lexp =
  Nl int |
  Vl vname |
  Plusl lexp lexp |
  LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
  "lval ( Nl n ) s = n" |
  "lval ( Vl x ) s = s x" |
  "lval ( Plusl a1 a2 ) s = lval a1 s + lval a2 s" |
  "lval ( LET x a1 a2 ) s = lval a2 ( s ( x := lval a1 s ) )"

fun inline :: "lexp \<Rightarrow> aexp" where
  "inline ( Nl n ) = aexp.N n" |
  "inline ( Vl x ) = aexp.V x" |
  "inline ( Plusl a1 a2 ) = aexp.Plus ( inline a1 ) ( inline a2 )" |
  "inline ( LET x t e ) = subst x ( inline t ) ( inline e )"

lemma "lval l s = aval ( inline l ) s"
  apply ( induction l  arbitrary: s )
  apply ( auto simp add: substitution_lemma)
done




datatype bexp =
  Bc bool |
  Not bexp |
  And bexp bexp |
  Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
  "bval ( Bc v ) s = v" |
  "bval ( Not b ) s = ( \<not> bval b s )" |
  "bval ( And b1 b2 ) s = ( bval b1 s \<and> bval b2 s )" |
  "bval ( Less a1 a2 ) s = ( aval a1 s < aval a2 s )"



fun not :: "bexp \<Rightarrow> bexp" where
  "not ( Bc True ) = Bc False" |
  "not ( Bc False ) = Bc True" |
  "not b = Not b"

lemma "not_lemma" : "bval ( not b ) s = bval ( Not b ) s"
  apply ( induction b )
  apply ( auto )
done



fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "and ( Bc True ) b = b" |
  "and b ( Bc True ) = b" |
  "and ( Bc False ) _ = Bc False" |
  "and _ ( Bc False ) = Bc False" |
  "and b1 b2 = And b1 b2"

lemma "and_lemma" : "bval ( and b1 b2 ) s = bval ( And b1 b2 ) s"
  apply ( induction b1 b2 rule: and.induct )
  apply ( auto )
done



fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "less ( aexp.N n1 ) ( aexp.N n2 ) = Bc ( n1 < n2 )" |
  "less a1 a2 = Less a1 a2"

lemma "less_lemma" : "bval ( less a1 a2 ) s = bval ( Less a1 a2 ) s"
  apply ( induction a1 a2 rule: less.induct )
  apply ( auto )
done



fun bsimp :: "bexp \<Rightarrow> bexp" where
  "bsimp ( Bc v ) = Bc v" |
  "bsimp ( Not b ) = not ( bsimp b )" |
  "bsimp ( And b1 b2 ) = and ( bsimp b1 ) ( bsimp b2 )" |
  "bsimp ( Less a1 a2 ) = less ( asimp a1 ) ( asimp a2 )"

lemma "bval ( bsimp b ) = bval b"
  apply ( induction b rule: bsimp.induct )
  apply ( auto split: bexp.split simp: not_lemma and_lemma less_lemma assimp_correct)
done



definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Le a1 a2 = Not ( Less a2 a1 )"

lemma "bval ( Le a1 a2 ) s = ( aval a1 s \<le> aval a2 s )"
  apply ( auto simp add: Le_def)
done

definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Eq a1 a2 = And ( Le a1 a2 ) ( Le a2 a1 )"

lemma "bval ( Eq a1 a2 ) s = ( aval a1 s = aval a2 s)"
  apply ( auto simp add: Eq_def Le_def )
done

end