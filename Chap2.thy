theory Chap2
imports Main
begin
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc ( add m n )"

lemma add_z [simp] : "add x 0 = x"
apply ( induction x )
apply ( auto )
done

lemma add_p [simp]: "add x (Suc y) = Suc ( add x y )"
apply ( induction x )
apply ( auto )
done

theorem add_com : "add x y = add y x"
apply ( induction y )
apply ( auto )
done


theorem add_ass : "add x ( add y z ) = add ( add x y ) z"
apply ( induction x )
apply ( auto )
done

fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0" |
  "double ( Suc x ) = Suc (  Suc ( double x )  )"

theorem double_add : "double x = add x x"
apply ( induction x )
apply ( auto )
done


fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count e Nil = 0" |
  "(count e (x # xs)) = (
   if x=e then
      Suc ( count e xs )
    else
      count e xs )"

theorem count_lt_length : "count x xs \<le> length xs"
apply ( induction xs )
apply ( auto )
done


fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc Nil x = [x]" |
  "snoc (x # xs) y = x # ( snoc xs y )"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse Nil = Nil" |
  "reverse ( x # xs ) = snoc ( reverse xs ) x"

lemma rev_snoc [simp] : "reverse ( snoc xs x ) = x # ( reverse xs )"
apply ( induction xs )
apply ( auto )
done

theorem rev_rev : "reverse ( reverse xs ) = xs"
apply ( induction xs )
apply ( auto )
done

fun sum :: "nat \<Rightarrow> nat" where
  "sum 0 = 0" |
  "sum ( Suc x ) = (Suc x) + (sum x)"

theorem sum_div : "sum x = ( x * (x+1) ) div 2"
  apply ( induction x )
  apply ( auto )
done

datatype 'a tree =
  Tip |
  Node  "'a tree"  'a  "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = Nil" |
  "contents ( Node t0 x t1 ) = x # ( contents t0 ) @ ( contents t1 )"

fun treesum :: "nat tree \<Rightarrow> nat" where
  "treesum Tip = 0" |
  "treesum ( Node t0 x t1 ) = x + ( treesum t0 ) + ( treesum t1 )"

theorem treesum_listsum : "treesum t = listsum ( contents t )"
  apply ( induction t )
  apply ( auto )
done

datatype 'a tree2 =
  Leaf 'a |
  Node "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror ( Leaf x ) = Leaf x" |
  "mirror ( Node t0 x t1 ) = Node ( mirror t1 ) x ( mirror t0 )"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order ( Leaf x ) = x # Nil" |
  "pre_order ( Node t0 x t1 ) = x # ( pre_order t0 ) @ ( pre_order t1 )"

fun pos_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pos_order ( Leaf x ) = x # Nil" |
  "pos_order ( Node t0 x t1 ) = ( pos_order t0 ) @ ( pos_order t1 ) @ x # Nil"

theorem pre_rev_pos : "pre_order ( mirror t ) = rev ( pos_order t )"
  apply ( induction t )
  apply ( auto )
done

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse a [] = []" |
  "intersperse a [x] = [x]" |
  "intersperse a (x # (y # xs)) = [x, a] @ ( intersperse  a  ( y # xs )  )"

theorem map_inter : "map f ( intersperse a xs ) = intersperse ( f a ) ( map f xs)"
apply ( induction a xs rule: intersperse.induct )
apply ( auto )
done


fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev []           ys = ys" |
  "itrev ( x # xs )   ys = itrev xs ( x # ys )"

lemma [simp] : "itrev xs ys = ( rev xs ) @ ys"
  apply ( induction xs arbitrary: ys)
  apply ( auto )
done

lemma "itrev xs [] = rev xs"
  apply ( induction xs )
  apply ( auto )
done

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 n = n" |
  "itadd (Suc m) n = itadd m ( Suc n )"

lemma "itadd m n = add m n"
  apply ( induction m arbitrary: n )
  apply ( auto )
done



datatype tree0 =
  Tip |
  Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip = 0" |
  "nodes ( Node t0 t1 ) = (nodes t0) + (nodes t1) + 1"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = explode n (Node t t)"

lemma "( nodes ( explode n t ) )  =  ( 2 ^ n ) * ( nodes t ) + ( 2 ^ n ) - 1"
  apply ( induction n arbitrary: t )
  apply ( auto simp add:algebra_simps )
done

fun option_bind :: "'a option \<Rightarrow> ( 'a \<Rightarrow> 'b option ) \<Rightarrow> 'b option" (infixr ">\<ge>" 100) where
  "option_bind None _ = None" |
  "option_bind ( Some a ) f = f a"

definition option_sum :: "int option \<Rightarrow> int option \<Rightarrow> int option" (infixr "+++" 260) where
  "(option_sum Mx My) = Mx >\<ge> (\<lambda>x . My >\<ge> (\<lambda> y . Some (x+y) ))"

definition option_mul :: "int option \<Rightarrow> int option \<Rightarrow> int option" (infixr "***" 260) where
  "(option_mul Mx My) = Mx >\<ge> (\<lambda>x . My >\<ge> (\<lambda> y . Some (x*y) ))"


datatype 'a exp =
  Var 'a |
  Cst int |
  Add "'a exp" "'a exp" |
  Mul "'a exp" "'a exp"

fun eval :: "'a exp \<Rightarrow> ('a \<Rightarrow> int option) \<Rightarrow> int option" where
  "eval ( Var i ) v = ( v i )" |
  "eval ( Cst x ) v = Some x" |
  "eval ( Add e0 e1 ) v = ( eval e0 v ) +++ ( eval e1 v )" |
  "eval ( Mul e0 e1 ) v = ( eval e0 v ) *** ( eval e1 v )"

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

theorem "Some ( evalp ( coeffs exp ) n) = eval exp (\<lambda> x . (Some n))"
  apply ( induction exp arbitrary: n)
  apply ( auto simp add:algebra_simps option_sum_def option_mul_def option_bind_def)
done

end