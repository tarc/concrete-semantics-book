theory Chap3
imports Main
begin

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp =
  N int |
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
  "asimp ( Plus a1 a2 ) = plus ( asimp a1 ) ( asimp a2)"

lemma "aval ( asimp a ) s = aval a s"
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
      ( Plus a11 a12      , N n  )              \<Rightarrow> ( Plus ( Plus a11 a12 ) ( N n ) ) |
      ( Plus a1' ( N n )  , V x  )              \<Rightarrow> ( Plus ( Plus a1' ( V x ) ) ( N n ) ) |
      ( Plus a11 a12      , V x  )              \<Rightarrow> ( Plus ( Plus a11 a12 ) ( V x ) ) |
      ( Plus a1' ( N n1 ) , Plus a2' ( N n2 ) ) \<Rightarrow> ( Plus ( Plus a1' a2' ) (N  (n1 + n2)) ) |
      ( Plus a1' ( N n )  , Plus a21 a22)       \<Rightarrow> ( Plus ( Plus a1' ( Plus a21 a22 ) ) ( N n ) ) |
      ( Plus a11 a12      , Plus a2' ( N n ) )  \<Rightarrow> ( Plus ( Plus a11 ( Plus  a12 a2' ) ) ( N n ) ) |
      ( Plus a11 a12      , Plus a21 a22 )      \<Rightarrow> ( Plus ( Plus a11 a12 ) ( Plus a21 a22 ) ) )"

lemma "aval ( full_asimp a ) s = aval a s"
  apply ( induction a )
  apply ( auto split: aexp.split)
done


end