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

end