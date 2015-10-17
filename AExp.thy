theory AExp
imports Main
begin

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp =
  N int |
  V vname |
  Plus aexp aexp |
  Times aexp aexp



fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |
  "aval (V x) s = s x" |
  "aval (Plus a1 a2) s = aval a1 s + aval a2 s" |
  "aval (Times a1 a2) s = aval a1 s * aval a2 s"



definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"

value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"



fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus ( N i1 ) ( N i2 ) = N ( i1 + i2 )"|
  "plus ( N i ) a = ( if  i = 0  then  a  else (  Plus ( N i ) a  ) )" |
  "plus a ( N i ) = ( if  i = 0  then  a  else (  Plus a ( N i )  ) )" |
  "plus a1 a2 = Plus a1 a2"

lemma aval_plus : "aval ( plus a1 a2 ) s = aval a1 s + aval a2 s"
  apply ( induction rule: plus.induct )
  apply ( auto )
done



fun times :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "times ( N n1 ) ( N n2 ) = N ( n1 * n2 )" |
  "times ( N n ) a =
    ( if
        n = 0 then N 0 else ( if
        n = 1 then a
        else Times ( N n ) a ) )" |
  "times a ( N n ) =
    ( if
        n = 0 then N 0 else ( if
        n = 1 then a
        else Times a ( N n ) ) )" |
  "times a1 a2 = Times a1 a2"


lemma "aval_times" : "aval ( times a1 a2 ) s = aval a1 s * aval a2 s"
  apply ( induction rule: times.induct )
  apply ( auto )
done



fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp ( N n ) = N n" |
  "asimp ( V x ) = V x" |
  "asimp ( Plus a1 a2 ) = plus ( asimp a1 ) ( asimp a2 )" |
  "asimp ( Times a1 a2 ) = times ( asimp a1 ) ( asimp a2 )"

value "asimp ( Times ( Times (N 3) (V x) ) (Plus (N (-1)) (N 21)) )"

lemma "aval ( asimp a ) s = aval a s"
  apply ( induction a )
  apply ( auto simp add: aval_plus aval_times)
done




fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal ( N n ) = True" |
  "optimal ( V x ) = True" |
  "optimal ( Plus ( N i ) ( N j ) ) = False" |
  "optimal ( Plus a1 a2 ) = ( optimal a1 \<and> optimal a2 )" |
  "optimal ( Times ( N i ) ( N j ) ) = False" |
  "optimal ( Times ( N n ) _ ) = ( n \<noteq> 0 \<and> n \<noteq> 1 )" |
  "optimal ( Times _ ( N n ) ) = ( n \<noteq> 0 \<and> n \<noteq> 1 )" |
  "optimal ( Times a1 a2 ) = ( optimal a1 \<and> optimal a2 )"


lemma "optimal_plus" : "optimal a1 \<Longrightarrow> optimal a2 \<Longrightarrow> optimal (plus a1 a2)"
  apply ( induction a1 a2 rule: plus.induct )
  apply ( auto )
done

lemma "optimal_times" : "optimal a1 \<Longrightarrow> optimal a2 \<Longrightarrow> optimal (times a1 a2)"
  apply ( induction a1 a2 rule: times.induct )
  apply ( auto )
done

lemma "optimal ( asimp a )"
  apply ( induction a )
  apply ( auto simp add: optimal_plus optimal_times )
done

end
