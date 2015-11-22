theory Chap5 imports Main
begin

lemma "\<not> surj ( f :: 'a \<Rightarrow> 'a set )"
proof
  assume 0 : "surj f"
  from this have "\<forall> A . \<exists> a . A = f a" by ( simp add: surj_def)
  from this have "\<exists> a . { x . x \<notin> f x } = f a" by blast
  from this have "\<exists> a . x \<in> f a = ( x \<notin> f a )" by blast
  from this show "False" by blast
qed

lemma
  assumes T : "\<forall> x y . T x y \<or> T y x"
      and A : "\<forall> x y . A x y \<and> A y x \<longrightarrow> x = y"
      and TA: "\<forall> x y . T x y \<longrightarrow> A x y"
      and "A x y"
    shows "T x y"
proof cases
  assume "T x y"
  thus "T x y" by simp
next
  assume "\<not> T x y"
  hence "T y x" using T by blast
  hence "A y x" using TA by blast
  hence "x = y" using assms by blast
  thus "T x y" using T by blast
qed


lemma "( \<exists> ys zs . xs = ys @ zs \<and> length ys = length zs )
     \<or> ( \<exists> ys zs . xs = ys @ zs \<and> length ys = length zs + 1 )"
proof cases
  assume "even ( length xs )"
    hence "\<exists> n . length xs = 2*n" by ( auto simp add: dvd_def )
    then obtain n where "length xs = 2*n" by blast
    let ?ys = "take n xs"
    let ?zs = "drop n xs"
    have "length ?ys = length ?zs" by (simp add: `length xs = 2 * n`)
    hence "xs = ?ys @ ?zs \<and> length ?ys = length ?zs" by simp
    hence "\<exists> ys zs . xs = ys @ zs \<and> length ys = length zs" by blast
  thus ?thesis by blast
next
  assume "odd ( length xs )"
    hence "\<exists> n . length xs = (2 * n) + 1" by presburger
    from this obtain n where "length xs = (2 * n) + 1" by blast
    let ?ys = "take ( n + 1 ) xs"
    let ?zs = "drop ( n + 1 ) xs"
    have "length ?ys = length ?zs + 1" by ( simp add: `length xs = (2 * n) + 1`)
    hence "xs = ?ys @ ?zs \<and> length ?ys = length ?zs + 1" by auto
    hence "\<exists> ys zs . xs = ys @ zs \<and> length ys = length zs + 1" by blast
  thus ?thesis by blast
qed


lemma "length(tl xs) = length xs - 1"
proof ( cases xs )
  assume "xs = []"
  thus ?thesis by simp
next
  fix y ys assume "xs = y # ys"
  thus ?thesis by simp
qed

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS : "ev n \<Longrightarrow> ev (Suc(Suc n))"

lemma "ev n \<Longrightarrow> ev ( n - 2 )"
proof -
  assume "ev n"
  from this have "ev ( n - 2 )"
  proof ( cases )
    case ev0 thus "ev ( n - 2 )" by ( simp add: ev.ev0 )
  next
    case (evSS k) thus "ev ( n - 2 )" by simp
  qed
  thus ?thesis by blast
qed

lemma "ev ( Suc m ) \<Longrightarrow> \<not> ev m"
proof ( induction "Suc m" arbitrary: m rule: ev.induct )
  fix n assume IH: "\<And> m . n = Suc m \<Longrightarrow> \<not> ev m"
  show "\<not> ev ( Suc n )"
  proof -- contradiction
    assume "ev ( Suc n )"
    thus False
    proof ( cases "Suc n" -- rule  )
      fix k assume "n = Suc k" "ev k"
      thus False using IH by auto
    qed
  qed
qed


lemma 
  assumes "ev n"
  shows "ev ( n - 2 )"
proof -
  show "ev ( n - 2 )" using `ev n`
  proof cases
    case ev0 thus "ev ( n - 2 )" by ( simp add: ev.ev0)
  next
    case evSS thus "ev ( n - 2 )" by simp
  qed
qed

lemma
  assumes a: "ev ( Suc ( Suc n ) )"
  shows "ev n"
proof -
  from a show "ev n" by cases
qed

lemma "\<not> ev ( Suc ( Suc ( Suc 0 ) ) )"
proof
  assume "ev ( Suc ( Suc ( Suc 0 ) ) )"
  thus False
  proof cases
    assume "ev ( Suc 0 )" hence False by cases
    thus False by blast
  qed
qed

inductive star :: "( 'a \<Rightarrow> 'a \<Rightarrow> bool ) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl  : "star r x x" |
  step  : "r x y  \<Longrightarrow>  star r y z  \<Longrightarrow>  star r x z"

inductive iter :: "( 'a \<Rightarrow> 'a \<Rightarrow> bool ) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl_i : "iter r 0 x x" |
  step_i : "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r ( n + 1 ) x z"

lemma "iter r n x y \<Longrightarrow> star r x y"
proof ( induction rule: iter.induct )
  fix x show "star r x x" by ( simp add: refl )
  fix x y n z assume "r x y" "star r y z"
  thus "star r x z" by ( metis step )
qed
  

fun elems :: "'a list \<Rightarrow> 'a set" where
  "elems [] = {}" |
  "elems ( a # as ) = { a } \<union> elems as"

lemma "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof ( induction xs rule: elems.induct )
  assume "x \<in> elems []"
  thus "\<exists> ys zs . [] = ys @ x # zs \<and> x \<notin> elems ys"  by simp

  next
  fix a as assume IH : "(x \<in> elems as \<Longrightarrow> \<exists>ys zs. as = ys @ x # zs \<and> x \<notin> elems ys)"
               and H : "x \<in> elems (a # as)"
  thus "\<exists>ys zs. a # as = ys @ x # zs \<and> x \<notin> elems ys"

  proof ( cases "x = a" )
    assume "x \<noteq> a"
    hence "x \<in> elems as" using H by auto
    hence "\<exists> ys zs . as = ys @ x # zs \<and> x \<notin> elems ys" using IH  by auto
    then obtain ys zs where "as = ys @ x # zs \<and> x \<notin> elems ys" by blast
      hence "a # as = (a # ys) @ x # zs \<and> x \<notin> elems ( a # ys )" using `x \<noteq> a` by auto
    thus "\<exists>ys zs. a # as = ys @ x # zs \<and> x \<notin> elems ys" by blast

  next
    assume "x = a"
    hence "a # as = [] @ x # as \<and> x \<notin> elems []" by auto
    thus ?thesis by blast

  qed
qed



datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
  emptyS  : "S []" |
  middl   : "S w \<Longrightarrow> S ( a # w @ [b] )" |
  doubl   : "S w \<Longrightarrow> S v \<Longrightarrow> S ( w @ v )"

inductive T :: "alpha list \<Rightarrow> bool" where
  emptyT  : "T []" |
  alter   : "T w \<Longrightarrow> T v \<Longrightarrow> T ( w @ a # v @ [b] )"


lemma TImpS : "T w \<Longrightarrow> S w"
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

lemma SImpT : "S w \<Longrightarrow> T w"
  apply ( induction rule: S.induct )
  apply ( rule emptyT )
  apply ( rule app_emp )
  apply ( rule alter )
  apply ( rule emptyT )
  apply ( assumption )
  apply ( metis doublT )
done

thm append_eq_append_conv_if leD

lemma "S w = T w" by ( metis SImpT TImpS )

lemma "S ( v @ w ) \<Longrightarrow> S ( v @ a # b # w )"
proof ( induction "v @ w" arbitrary: v w rule: S.induct )

  fix v :: "alpha list" and w assume
    E : "[] = v @ w"
    show "S ( v @ a # b # w )"
  proof -
    have "S ( a # [] @ [b] )" by ( metis middl emptyS )
    hence "S ( a # [b] )" by simp
    moreover have "v=[]" using E by simp
    moreover have "w=[]" using E by simp
    ultimately show "S ( v @ a # b # w )" by simp
  qed

  next
  fix w v w' assume
    H : "S w" and
    IH : "\<And>v w' . w = v @ w' \<Longrightarrow> S ( v @ a # b # w' )" and
    EH : "a # w @ [b] = v @ w'"
    show "S ( v @ a # b # w' )"
  proof ( cases "v = []" )
    assume "v = []" show "S ( v @ a # b # w' )"
    proof -
      have "w' = a # w @ [b]" using `v = []` EH by simp
      moreover hence "S ( w' )" using H by ( metis middl )
      moreover hence "S ( v @ a # [ b ] )" using `v = []` by ( metis append_Nil emptyS middl )
      ultimately have "S ( ( v @ a # [ b ] ) @ w' )" by ( metis doubl )
      thus "S ( v @ a # b # w' )" by simp
    qed

    next
    assume "v \<noteq> []" show "S ( v @ a # b # w' )"
    proof ( cases "w' = []" )
      assume "w' = []" show "S ( v @ a # b # w' )"
      proof -
        have "v = a # w @ [b]" using `w' = []` EH by simp
        moreover hence "S ( v )" using H by ( metis middl )
        moreover hence "S ( v @ a # [ b ] )" by ( metis emptyS middl doubl append_Nil )
        ultimately have "S ( v @ a # [ b ] @ w' )" using `w' = []` by simp
        thus "S ( v @ a # b # w' )" by simp
      qed

      next
      assume "w' \<noteq> []" show "S ( v @ a # b # w' )"
      proof -
        have "v @ w' = ( hd v ) # ( tl v ) @ w'" using `v \<noteq> []` by simp
        hence V: "w @ [ b ] = tl v @ w' \<and> hd v = a" using `v \<noteq> []` EH by ( metis list.inject )
        hence "w @ [ b ] = ( tl v @ butlast w' ) @ [ last w' ]" using `w' \<noteq> []` by simp
        hence W': "w = tl v @ butlast w' \<and> last w' = b" by ( metis append1_eq_conv )
        hence "S ( tl v @ butlast w' )" using H by metis
        hence "S ( tl v @ a # b # butlast w' )" using IH W' by metis
        hence "S ( a # (tl v @ a # b # butlast w' ) @ [ b ] )" by ( metis middl )
        hence "S ( ( a # tl v ) @ [a,b] @ ( butlast w' @ [ b ] ) )" by simp
        moreover have "a # tl v = v" using V list.collapse `v \<noteq> []` by force
        moreover have "butlast w' @ [ b ] = w'" using W' append_butlast_last_id `w' \<noteq> []` by force
        ultimately show "S (  v @ a # b # w' )" by simp
      qed
    qed
  qed

  next
  fix w v p s assume
    W : "S w"
    "\<And>p s. w = p @ s \<Longrightarrow> S ( p @ a # b # s )" and
    V : "S v"
    "\<And>p s. v = p @ s \<Longrightarrow> S ( p @ a # b # s )" and
    EH : "w @ v = p @ s"
    show "S ( p @ a # b # s )"
  proof ( cases "length p = length w" )
    assume LH : "length p = length w" show "S ( p @ a # b # s )"
    proof -
      have "S ( a # [ b ] )" by ( metis emptyS middl append_Nil)
      moreover have "w = p \<and> v = s" using EH LH by simp
      ultimately have "S ( p @ [ a , b ] @ s )" using W V by ( metis doubl )
      thus ?thesis by simp
    qed

    next
    assume LD : "length p \<noteq> length w" show "S ( p @ a # b # s )"
    proof ( cases "length p < length w" )
      assume LPLTLW : "length p < length w" show "S ( p @ a # b # s )" 
      proof -
        have "w = take ( length p ) w @ drop ( length p ) w" using LPLTLW by simp
        moreover have PS : "p = take ( length p ) w \<and>
                              s = drop ( length p ) w @ v"
                                using EH LPLTLW by (metis append_eq_append_conv_if leD)
        ultimately have "w = p @ drop ( length p ) w" by simp
        hence "S ( p @ a # b # drop ( length p ) w )" using W  by metis
        hence "S ( ( p @ a # b # drop ( length p ) w ) @ v )" using V by ( metis doubl )
        thus "S ( p @ a # b # s )" using PS by simp
      qed

      next
      assume LNL : "\<not> length p < length w" show "S ( p @ a # b # s )"
      proof -
        have "length p > length w" using LD LNL by ( metis linorder_class.less_linear )
        moreover hence "length w = length ( take ( length w ) p )" by simp
        moreover have "w @ v = take ( length w ) p @ drop ( length w ) p @ s" using EH by simp
        ultimately have 
          "w = take ( length w ) p \<and>
            v = drop ( length w ) p @ s" by ( metis append_eq_append_conv )
        moreover hence "S ( drop ( length w ) p @ a # b # s )" using V by metis
        ultimately have "S ( take ( length w ) p @ drop ( length w ) p @ a # b # s )"
          using W by ( metis doubl )
        thus ?thesis by ( metis append_take_drop_id  append_assoc )
      qed
    qed
  qed
qed


fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
  "balanced 0 [] = True" |
  "balanced _ [] = False" |
  "balanced 0 ( b # _ ) = False" |
  "balanced n ( a # w ) = balanced ( Suc n ) w" |
  "balanced ( Suc n ) ( b # w ) = balanced n w"

value "balanced 1 [b]"

lemma "balanced n w \<Longrightarrow> S ( replicate n a @ w )"
  proof ( induction n w rule: balanced.induct )
  assume "balanced 0 []" thus "S ( replicate 0 a @ [] )" using emptyS replicate_0 by auto

  next
  fix v assume
    H : "balanced ( Suc v ) []"
    show "S ( replicate ( Suc v ) a @ [] )"
  proof -
    have False using H by simp
    thus ?thesis by metis
  qed

  next
  fix as assume
    H : "balanced 0 ( b # as )"
    show "S ( replicate 0 a @ b # as )"
  proof -
    have False using H by simp
    thus ?thesis by metis
  qed

  next
  fix n w assume
    IH : "balanced ( Suc n ) w \<Longrightarrow> S ( replicate ( Suc n ) a @ w )" and
    H  : "balanced n ( a # w )"
    show "S ( replicate n a @ a # w )"
  proof -
    have "balanced ( Suc n ) w" using H by simp
    hence "S ( replicate ( Suc n ) a @ w )" using IH by metis
    hence "S ( a # replicate n a @ w )" by simp
    thus ?thesis using replicate_app_Cons_same by metis
  qed

  next
  fix n w assume
    IH : "balanced n w \<Longrightarrow> S ( replicate n a @ w )" and
    H  : "balanced ( Suc n ) ( b # w )"
    show "S ( replicate ( Suc n ) a @ b # w )"
  proof -
    have "balanced n w" using H by simp
    hence "S ( replicate n a @ w )" using IH by metis

    



end