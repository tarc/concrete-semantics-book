theory Exp
imports Main
begin

fun option_bind :: "'a option \<Rightarrow> ( 'a \<Rightarrow> 'b option ) \<Rightarrow> 'b option" where
  "option_bind None _ = None" |
  "option_bind ( Some a ) f = f a"

definition option_sum :: "int option \<Rightarrow> int option \<Rightarrow> int option" where
  "(option_sum Mx My) = option_bind Mx (\<lambda>x . option_bind My (\<lambda> y . Some (x+y) ))"

definition option_mul :: "int option \<Rightarrow> int option \<Rightarrow> int option" where
  "(option_mul Mx My) = option_bind Mx (\<lambda>x . option_bind My (\<lambda> y . Some (x*y) ))"

datatype 'a exp =
  Var 'a |
  Cst int |
  Add "'a exp" "'a exp" |
  Mul "'a exp" "'a exp"

fun eval :: "'a exp \<Rightarrow> ('a \<Rightarrow> int option) \<Rightarrow> int option" where
  "eval ( Var i ) v = ( v i )" |
  "eval ( Cst x ) v = Some x" |
  "eval ( Add e0 e1 ) v = option_sum ( eval e0 v ) ( eval e1 v )" |
  "eval ( Mul e0 e1 ) v = option_mul ( eval e0 v ) ( eval e1 v )"

value "( Mult ( Add ( Var 0 ) ( Cst 0 ) ) Cst 3 )"

value "\<lambda> x. ( if x=0 then Some 2 else None )"

value "(eval
        ( Mult ( Add ( Var 0 ) ( Cst 0 ) ) Cst 3 )
        (\<lambda> x. ( if x=0 then Some 3 else None )))"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] _ = 0" |
  "evalp (c0 # cs) x = c0 + x * ( evalp cs x )"

fun sump :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "sump [] l1 = l1" |
  "sump l0 [] = l0" |
  "sump (x#xs) (y#ys) = (x+y) # ( sump xs ys )"

lemma "evalp xs n + evalp ys n = evalp (sump xs ys ) n"
proof (induction xs arbitrary:ys n)
case Nil
  show ?case by simp
next
  have "evalp (a # xs) n + evalp ys n = evalp (sump (a # xs) ys) n"
  proof (induction ys)
    case Nil
      show ?case by simp
    next
      have "evalp (sump (a # xs) (aa # ys)) n = evalp ((a+aa) #sump xs ys) n" by (simp)
done

fun cmulp :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "cmulp c [] = []" |
  "cmulp c (p # ps) = (c*p) # (cmulp c ps)"

fun mulp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "mulp [] p = []" |
  "mulp (a # as) p = sump (cmulp a p) (0 # (mulp as p))"

fun coeffs :: "unit exp \<Rightarrow> int list" where
  "coeffs (Var ()) = [0, 1]" |
  "coeffs (Cst c ) = [c]" |
  "coeffs (Add e0 e1) = sump (coeffs e0) (coeffs e1)" |
  "coeffs (Mul e0 e1) = mulp (coeffs e0) (coeffs e1)"

lemma [simp]: "option_sum (Some x) (Some y) = Some (x + y)"
  apply ( simp add: option_sum_def )
done


theorem "eval e (\<lambda> x . (Some n)) = Some ( evalp ( coeffs e ) n)"
  apply ( induction e arbitrary:n )
  apply ( auto )
done

end