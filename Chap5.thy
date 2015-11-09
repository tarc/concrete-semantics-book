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



end