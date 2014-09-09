Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finfun finset bigop.
Require Import Reals Fourier.
Require Import Reals_ext log2 ssr_ext Rbigop proba entropy aep typ_seq natbin Rssr ceiling v_source_code divergence channel.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope tuple_ext_scope.
Local Open Scope typ_seq_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope entropy_scope.
Local Open Scope divergence_scope.
Local Open Scope channel_scope.

(* ctr c + ctr v => Command input*)
(* ctr c + ctr v + Search " _ " or ctr c + ctr l *)
(* boolのイコールを示すには apply /_____ /____. _____はview(ifPとか)をかける *)
(* nesym = not_eq_sym
     : forall (A : Type) (x y : A), x <> y -> y <> x *)
Section Jensen.

Variable A :finType.
Variable f : R -> R.

Definition convex := forall x y t : R, 0 <= t <= 1->
f (t * x + (1 - t) * y) <= t * f x + (1 - t) * f y.

Lemma Jensen's_inequality :forall (X : rvar A), convex->
f (`E X) <= \rsum_(a | a \in A) f (X a) * `p_ X a.
Proof. 
move=> X convex; move:(enum_uniq A) X (pmf1 (rv_dist X)).
rewrite enumT /Ex_alt /index_enum /index_iota.
elim:(Finite.enum _) => [_ X | hd tl IH].
  rewrite big_nil=> contra.
  by move:R1_neq_R0; rewrite contra.
case/andP=>a_not l_uniq X. 
rewrite !big_cons inE.
move/(Rplus_eq_compat_l (- `p_ X hd)).
rewrite addRA Rplus_opp_l add0R addRC.
case: (Req_dec (1- `p_ X hd) 0) => [/Rminus_diag_uniq dist_eq_1| dist_not_eq_1].
  (*case \rsum `p_ X = 1*)
  rewrite dist_eq_1 Rplus_opp_r.
  move/esym; rewrite big_uniq//.
  move/(Req_0_rmul_inv _ _ (Rle0f `p_ X))=> intl_p0.
  have Htmp: forall g, 0 = \big[Rplus/0]_(j <- tl | j \in A) (g j * `p_ X j).
    move=>g; rewrite big_uniq //.
    by apply:Req_0_rmul=>i ?; rewrite -(intl_p0 i) // mulR0.
  by rewrite -!Htmp !addR0 -dist_eq_1 !mulR1; apply: Rle_refl. 
(*case \rsum `p_ X <> 1*)
have le_dist_1: 0 < (1 + - `p_ X hd).
  apply:(Rplus_gt_reg_l (`p_ X hd)).
  rewrite addRC -addRA Rplus_opp_l !addR0.
  move:(dist_max `p_ X hd) dist_not_eq_1.
  by case=>//; move->; rewrite /Rminus Rplus_opp_r.
move/(Rmult_eq_compat_r (/(1 + - `p_ X hd))).
rewrite !(big_morph _ (morph_mulRDl _) (mul0R _)).
rewrite -(Rinv_r_sym (1 + - `p_ X hd) dist_not_eq_1)=> Hpmf1.
rewrite -(mulR1 (\big[Rplus/0]_(j <- tl | j \in A) (X j * `p_ X j))). 
rewrite (Rinv_r_sym (1 - `p_ X hd)) //.
rewrite (addRC (X hd * _) _) (addRC (f (X hd) * _) _).
rewrite mulRC -mulRA addRC mulRC.
(*  pose t := `p_ X hd.
    pose y := (/(1 - t) *\big[Rplus/0]_(j <- tl | j \in A) (X j * `p_ X j)).
    pose x := (X hd).*)
apply:(Rle_trans _ ((`p_ X hd) * f (X hd) + (1 - `p_ X hd) * 
                  f ((/ (1 - `p_ X hd) * \big[Rplus/0]_(j <- tl | j \in A) (X j * `p_ X j))))).
  by apply: (convex _ _ _  (conj ((Rle0f (`p_ X) hd)) (dist_max (`p_ X) hd))).
rewrite mulRC addRC mulRC.
apply:Rplus_le_compat_r.
apply:(Rmult_le_reg_r (/(1 + - `p_ X hd))); first by apply:Rinv_0_lt_compat.
rewrite -mulRA -Rinv_r_sym; last by apply:dist_not_eq_1.
rewrite mulR1 mulRC.
rewrite !(big_morph _ (morph_mulRDl _) (mul0R _)).

pose pos_f' x := if (x \in tl) then (`p_ X x * / (1 + - `p_ X hd)) else 0.
have Rle0f' x: 0 <= pos_f' x. 
  rewrite/pos_f'; case:ifP =>[_ | _]; last by apply: Rle_refl.
  by apply:(Rle_mult_inv_pos _ _ (Rle0f (`p_ X) x)).
pose pmf' := mkPosFun Rle0f'.
have pmf1': \big[Rplus/0]_(j| j \in A ) pmf' j = 1.
  rewrite -Hpmf1  [in RHS]big_seq_cond [in RHS]big_mkcondl /=. 
  rewrite (bigID (fun x => x \in tl)) /= /pos_f' (big_uniq _ l_uniq) /=.
  rewrite -{2}(addR0 (\rsum_(i | i \in tl) _)); apply: Rplus_eq_compat_l.
  by apply:esym; apply/Req_0_rmul => i; move/negb_true_iff ->. 
pose dist' := mkDist pmf1'.
pose rvar' := mkRvar  dist' (rv_fun X).
have tmp:forall f, \big[Rplus/0]_(j <- tl | j \in A) (f (X j) * `p_ X j * / (1 + - `p_ X hd)) = 
       \big[Rplus/0]_(j <- tl | j \in A) (f (rvar' j) * (`p_ rvar' j )).
  move=> f0.
  rewrite big_seq_cond [in RHS]big_seq_cond !big_mkcondl /=.
  by apply:eq_bigr => i _; rewrite /pos_f'; case:ifP; first rewrite mulRA.
rewrite tmp (tmp (fun x => x)); apply:(IH l_uniq).
by rewrite /= /pos_f' -{2}Hpmf1 [in RHS]big_seq_cond !big_mkcondl.
Qed.

End Jensen.

Section log_sum.
Variable A : finType.

Lemma Rlt_big_0_posf: forall f : A -> R+, (exists a, 0 < f a) -> 0 < \rsum_(i | i \in A) f i.
Proof.
move=>f; case=> a fa_pos.
rewrite big_seq -big_seq /index_enum.
rewrite (bigD1_seq a) // /=; last by rewrite -enumT; move:(enum_uniq A).
apply: (Rplus_lt_le_0_compat _ _ fa_pos).
by apply: Rle_big_0_P_g; move: (Rle0f f).
Qed.

Variable f g: A -> R+.
Hypothesis f_dom_by_g : f << g.

Lemma log_sum_inequality :
  \rsum_(a|a \in A) (f a * (log (f a) - log (g a))) >= 
  (\rsum_(a|a \in A) f a) * (log (\rsum_(a|a \in A) f a) - log (\rsum_(a|a \in A) g a)).
Proof.
rewrite [X in X >= _](_ : _ = - \rsum_(a | a \in A) f a * (log (g a) - log (f a))); last first.
  rewrite (big_morph _ morph_Ropp Ropp_0).
  by apply:eq_bigr => ? _; rewrite -Ropp_mult_distr_r_reverse Ropp_minus_distr.
rewrite [X in _ >= X](_ : _ = - (\rsum_(a | a \in A) f a) * (log (\rsum_(a | a \in A) g a) - log (\rsum_(a | a \in A) f a))); last first.
  by rewrite Ropp_mult_distr_l_reverse -Ropp_mult_distr_r_reverse Ropp_minus_distr.
rewrite Ropp_mult_distr_l_reverse; apply:Ropp_le_ge_contravar; apply:Rminus_le.
rewrite {1}/Rminus (big_morph _ (morph_mulRDl _) (mul0R _)) (big_morph _ morph_Ropp Ropp_0).
rewrite [X in X <= 0](_ : _ = \rsum_(a | a \in A) f a * (log (g a) - log (f a) - (log (\rsum_(i | i \in A) g i) - (log (\rsum_(i | i \in A) f i))))); last first.
  by rewrite -big_split; apply:eq_bigr=>i _; rewrite [in RHS]Rmult_minus_distr_l.
rewrite [X in X <= 0](_ : _ = \rsum_(a | a \in A) f a * (log (g a *
      (\rsum_(i | i \in A) f i)) - log (f a * (\rsum_(i | i \in A) g i)))); last first.
  apply: eq_bigr=> i _.
  case:(Rle0f g i)=> [lt_0_gi | ].
    case: (Rle0f f i)=> [lt_0_fi | <- ]; last by rewrite !mul0R.
    apply: Rmult_eq_compat_l. 
    rewrite !log_mult//; last first. 
        by apply:Rlt_big_0_posf; apply:(ex_intro _ i).
      by apply:Rlt_big_0_posf; apply:(ex_intro _ i).
    rewrite /Rminus Ropp_minus_distr Ropp_plus_distr /Rminus -!addRA; apply:Rplus_eq_compat_l.
    by rewrite !addRA addRC [in RHS]addRC; apply:Rplus_eq_compat_l; rewrite addRC.
  by move/esym /(f_dom_by_g) ->; rewrite !mul0R.
have: (0 <= \rsum_(i | i \in A) g i) by apply: Rle_big_0_P_g; move: (Rle0f g).
case=> [lt_big_0| eq_big_0]; last first .
  apply:Rfourier_eqRL_to_le; apply:Req_0_rmul=> i _.
  move:eq_big_0; move/(Req_0_rmul_inv _ g (Rle0f g))=> gi_0.
  have: g i = 0 by rewrite (gi_0 i).
  by move/f_dom_by_g->; rewrite mul0R.
apply: (Rmult_le_reg_r (\rsum_(i | i \in A) g i))=>//.
rewrite mul0R (big_morph _ (morph_mulRDl _) (mul0R _)). 
rewrite [X in X <= 0](_ : _ = \rsum_(i | i \in A)
                               f i * (\rsum_(i0 | i0 \in A) g i0) *
                              (log (g i * (\rsum_(i0 | i0 \in A) f i0)) -
                               log (f i * (\rsum_(i0 | i0 \in A) g i0)))); last first.
  by apply:eq_bigr=> i _; rewrite -!mulRA;  apply: Rmult_eq_compat_l; rewrite mulRC.
apply:(Rle_trans _ ((\rsum_(i | i \in A) ((g i * (\rsum_(i0 | i0 \in A) f i0) - 
                                       (f i * (\rsum_(i0 | i0 \in A) g i0))))) * log (exp 1))).
  rewrite (big_morph _ (morph_mulRDl _) (mul0R _)).
  apply:Rle_big_P_f_g => a _; apply: div_diff_ub.
      by move: lt_big_0; move/Rlt_le=>?; apply: (Rmult_le_pos _ _ (Rle0f f a) _).
    by apply:(Rmult_le_pos _ _ (Rle0f g a)); apply: Rle_big_0_P_g; move: (Rle0f f).
  case/Rmult_integral=> [ /f_dom_by_g -> |le_0_sum]; first by rewrite mul0R.
(*  suff -> : f a = 0 by rewrite mul0R.*)
  rewrite (_: f a = 0); first by rewrite mul0R.
  apply:esym; move/esym:le_0_sum=> eq_0_sum.
  by apply:(Req_0_rmul_inv _ f (Rle0f f) eq_0_sum).
rewrite -{4}(mul0R (log (exp 1))); apply:Rmult_le_compat_r; first by apply:log_exp1_Rle_0.
rewrite big_split -(big_morph _ morph_Ropp Ropp_0) -!(big_morph _ (morph_mulRDl _) (mul0R _)).
by rewrite /= mulRC Rplus_opp_r; apply:Rle_refl.
Qed.

End log_sum.

Section log_sum_nat.

Lemma Rlt_big_0_posf_nat n m: forall f : nat -> R+, (exists a, a \in index_iota m n /\ 0 < f a) -> 0 < \rsum_(m<= i < n) f i.
Proof.
move=>f; case=> a [ain fa_pos].
rewrite big_seq -big_seq /index_enum.
rewrite (bigD1_seq a) // /=; last exact: iota_uniq.
apply: (Rplus_lt_le_0_compat _ _ fa_pos).
rewrite -(add0n m) big_addn.
by rewrite big_mkord; apply: Rle_big_0_P_g=> i _; move:(Rle0f f).
Qed.

Variable n m: nat.
Variable f g: nat -> R+.
Hypothesis f_dom_by_g : f << g.
Hypothesis le_m_n: (leq m n)%N.

Lemma log_sum_inequality_nat:
  \rsum_(m <= i < n) (f i * (log (f i) - log (g i))) >= 
  (\rsum_(m <= i < n) f i) * (log (\rsum_(m <= i < n) f i) - log (\rsum_(m <= i < n) g i)).
Proof.
rewrite [X in X >= _](_ : _ = - \rsum_(m <= i < n) f i * (log (g i) - log (f i))); last first.
  rewrite (big_morph _ morph_Ropp Ropp_0).
  by apply:eq_bigr => ? _; rewrite -Ropp_mult_distr_r_reverse Ropp_minus_distr.
rewrite [X in _ >= X](_ : _ = - (\rsum_(m <= i < n) f i) * (log (\rsum_(m <= i < n) g i) - log (\rsum_(m <= i < n) f i))); last first.
  by rewrite Ropp_mult_distr_l_reverse -Ropp_mult_distr_r_reverse Ropp_minus_distr.
rewrite Ropp_mult_distr_l_reverse; apply:Ropp_le_ge_contravar; apply:Rminus_le.
rewrite {1}/Rminus (big_morph _ (morph_mulRDl _) (mul0R _)) (big_morph _ morph_Ropp Ropp_0).
rewrite [X in X <= 0](_ : _ = \rsum_(m <= i < n) f i * (log (g i) - log (f i) - (log (\rsum_(m <= j < n) g j) - (log (\rsum_(m <= j< n) f j))))); last first.
  by rewrite -big_split; apply:eq_bigr=>i _; rewrite [in RHS]Rmult_minus_distr_l.
rewrite [X in X <= 0](_ : _ = \rsum_(m <= i < n) f i * (log (g i *
      (\rsum_(m <= j < n) f j)) - log (f i * (\rsum_(m <= j < n) g
      j)))); last first.
  apply:eq_big_nat=> i ?.
  case:(Rle0f g i)=> [lt_0_gi | ].
    case: (Rle0f f i)=> [lt_0_fi | <- ]; last by rewrite !mul0R.
    apply: Rmult_eq_compat_l. 
    rewrite !log_mult//; last first. 
        apply:Rlt_big_0_posf_nat; apply:(ex_intro _ i).
        by apply:conj=>//; rewrite mem_iota subnKC //.
      apply:Rlt_big_0_posf_nat; apply:(ex_intro _ i).
      by apply:conj=>//; rewrite mem_iota subnKC //.
    rewrite /Rminus Ropp_minus_distr Ropp_plus_distr /Rminus -!addRA; apply:Rplus_eq_compat_l.
    by rewrite !addRA addRC [in RHS]addRC; apply:Rplus_eq_compat_l; rewrite addRC.
  by move/esym /(f_dom_by_g) ->; rewrite !mul0R.
have: (0 <= \rsum_(i<-index_iota m n) g i).
  by rewrite -(add0n m) big_addn big_mkord; apply: Rle_big_0_P_g=> i _; move:(Rle0f g).
case=>[lt_big_0|]; last first.
  rewrite -(add0n m) !big_addn !big_mkord=> eq_big_0.
  apply:Rfourier_eqRL_to_le; apply:Req_0_rmul=> i _.
  have Rle0g: forall x: ordinal_finType (n - m), 0 <= g (addn (@nat_of_ord _ x) m)%N.
    by move=> x; apply:(Rle0f g).
  move/(Req_0_rmul_inv _ _ Rle0g):eq_big_0=> gi_0.
  have: g (addn i m)%N = 0 by rewrite (gi_0 i).
  by move/f_dom_by_g->; rewrite mul0R.
apply:(Rmult_le_reg_r (\rsum_(i<-index_iota m n) g i) _ _ lt_big_0).
rewrite mul0R (big_morph _ (morph_mulRDl _) (mul0R _)). 
rewrite [X in X <= 0](_ : _ = \rsum_(m <= j < n)
                               f j * (\rsum_(m <= k < n) g k) *
                              (log (g j * (\rsum_(m <= k < n) f k)) -
                               log (f j * (\rsum_(m <= k < n) g k)))); last first.
  by apply:eq_bigr=> i _;  rewrite -!mulRA;  apply: Rmult_eq_compat_l; rewrite mulRC.
apply:(Rle_trans _ ((\rsum_(m <= j < n) ((g j * (\rsum_(m <= k < n) f k) - 
                                       (f j * (\rsum_(m <= k < n) g k))))) * log (exp 1))).
  rewrite (big_morph _ (morph_mulRDl _) (mul0R _)) -(add0n m) !big_addn !big_mkord.
  move:lt_big_0; rewrite -(add0n m) big_addn big_mkord => le_big_0.
  apply:Rle_big_P_f_g => a _; apply:div_diff_ub.
  apply:Rmult_le_pos; first by apply:(Rle0f f).
  by apply: Rle_big_0_P_g; move: (Rle0f g).
    have le_bigf_0: (0 <= \rsum_(i<n - (0 + m)) f (addn i (0 + m))).
      by apply: Rle_big_0_P_g; move: (Rle0f f).
    by apply:Rmult_le_pos=> //;first apply:(Rle0f g).
  case/Rmult_integral=> [ /f_dom_by_g -> |le_0_sum]; first by rewrite mul0R.
  rewrite (_: f (addn a (0 + m)) = 0); first by rewrite mul0R.
  apply:esym; move/esym:le_0_sum=> eq_0_sum.
  have Rle0f': forall x: ordinal_finType (n - m), 0 <= f (addn (@nat_of_ord _ x) m)%N.
    by move=> x; apply:(Rle0f f).
  by apply:(Req_0_rmul_inv _ _  Rle0f' eq_0_sum).
rewrite -{4}(mul0R (log (exp 1))); apply:Rmult_le_compat_r; first by apply:log_exp1_Rle_0.
rewrite big_split /=.
rewrite -(big_morph _ morph_Ropp Ropp_0) -!(big_morph _ (morph_mulRDl _) (mul0R _)).
by rewrite mulRC Rplus_opp_r; apply:Rle_refl.
Qed.

End log_sum_nat.

Section Ordinal.

Variable T : finType.
Variable f : T -> nat.

Definition inordf t := inord (f t) : 'I_(\max_t f t).+1.

Lemma inordf_eq : f =1 inordf.
Proof.
 move => t.  rewrite /inordf inordK //.  by apply: leq_bigmax.
Qed.
End Ordinal.
Prenex Implicits inordf.

Section big_pow.

Variable x : R.
Hypothesis neq_x_1 : x <> 1.

Lemma big_pow n m: \rsum_(m <= i < n.+1) x ^ i =  x ^ m * (1 - (x ^ (n.+1 - m))) / (1 - x).
Proof.
move/nesym /Rminus_eq_contra:neq_x_1=> ?.
move/orP:(leq_total n m)=>[|].
  move:(leq_eqVlt n m)->; move/orP=>[/eqP -> | ].
  by rewrite big_nat1 -addn1 addnC subSn // subnn pow_1 /Rdiv -mulRA -Rinv_r_sym // mulR1.
  rewrite/leq; move/eqP=>nm0.
  rewrite -{1}(add0n m) big_addn /= nm0.
  by rewrite big_nil /= /Rminus Rplus_opp_r mulR0 /Rdiv mul0R.
move:n; elim:m=> [n le_0_n| m' IH n le_m'_n].
  elim n=> [|n' IH]; first by rewrite  big_nat1 pow_O subn0 pow_1 mul1R /Rdiv -Rinv_r_sym //.
  rewrite big_nat_recr /= IH pow_O !mul1R .
  apply:(Rmult_eq_reg_r (1 - x))=>//.
  rewrite Rmult_plus_distr_r /Rdiv -mulRA -[in RHS]mulRA -!Rinv_l_sym // !mulR1.
  rewrite Rmult_plus_distr_l mulR1 addRA /Rminus.
  by rewrite -(addRA 1 (- x ^ n'.+1) _) Rplus_opp_l addR0 mulRC Ropp_mult_distr_l_reverse.
rewrite big_add1 -{1}(add0n m') big_addn /=.
rewrite [X in X = _](_ : _ = x * \rsum_(i<-index_iota 0 (n - m')) x ^ (i + m')); last first.
  by rewrite mulRC (big_morph _ (morph_mulRDl _) (mul0R _)); apply:eq_bigr=>? _; rewrite mulRC.
rewrite (_ : \rsum_(i<-index_iota 0 (n - m')) x ^ (i + m') = 
             \rsum_(i<-index_iota 0 (n - m').+1.-1) x ^ (i + m')) //.
rewrite (_ :  \rsum_(i<-index_iota 0 (n - m').+1.-1) x ^ (i + m') = 
              \rsum_(i<-index_iota m' n) x ^ i); last first.
 by rewrite -{3}(add0n m') big_addn.
move:(ltn_predK le_m'_n)=>-n0_m1p1.
rewrite -{1}n0_m1p1 IH; last by rewrite/leq -subSS n0_m1p1.
by rewrite mulRA mulRA [in RHS]subSn // (subnSK _) /Rdiv // n0_m1p1.
Qed.

Lemma big_pow1 n: \rsum_(1 <= i < n.+1) x ^ i = x * (1 - (x ^ n)) / (1 - x).
Proof.
by rewrite big_pow  pow_1 subn1.
Qed.

Lemma log_pow n r: 0 < r -> log (r ^ n) = (INR n) * log r.
Proof.
elim:n=> [|n' IH lt_0_r]; first by rewrite log_1 mul0R.
rewrite log_mult//;last by apply:pow_lt.
by rewrite IH // -addn1 addRC plus_INR Rmult_plus_distr_r mul1R.
Qed.

End big_pow.

Section converse.

Variable A : finType.
Variable P : dist A.
Variable to_nat : A -> nat.
Let X := mkRvar P (fun x => INR (to_nat x)).

Lemma dist_nat : \rsum_(0 <= i < (\max_(a| a \in A) to_nat a).+1) Pr[X = (INR i)] = 1.
Proof.
rewrite -(pmf1 P).
rewrite [in RHS](partition_big (fun a => (inordf to_nat) a) 
            (fun i => i \in 'I_(\max_(a | a \in A) to_nat a).+1)) //=.
rewrite big_mkord.
apply:eq_bigr=> i H.
apply:eq_bigl=>i0.
rewrite /= inE.
apply/eqP/eqP; first by move/INR_eq; rewrite inordf_eq; apply:ord_inj.
by rewrite inordf_eq; move->.
Qed.

Lemma Ex_nat : `E X = 
               \rsum_(0 <= i < (\max_(a| a \in A) to_nat a).+1) (INR i) * Pr[X = (INR i)].
Proof.
rewrite /Ex_alt.
rewrite (partition_big (fun a => (inordf to_nat) a) 
            (fun i => i \in 'I_(\max_(a | a \in A) to_nat a).+1)) //=.
pose n1 := (\max_(a in A) to_nat a).
rewrite (_ : \rsum_(0 <= i < n1.+1) INR i * Pr[X = (INR i)] = 
             \rsum_(i | i \in 'I_n1.+1) INR i * Pr[X = (INR i)]); last first.
  rewrite /index_iota subn0 -val_enum_ord.
  rewrite big_map big_uniq /=; last apply:enum_uniq.
  by apply:eq_bigl=> i; first rewrite /= mem_enum.
apply:eq_bigr=> i H.
rewrite /@pr /Pr mulRC (big_morph _ (morph_mulRDl _) (mul0R _)).
rewrite (_ : \rsum_(i0 | i0 \in _) `p_ X i0 * INR i =
             \rsum_(i0 | i0 \in [set x | X x == INR i]) INR i * `p_ X i0); last first.
  by apply:eq_bigr=> a _; rewrite mulRC.
rewrite ( _ : \rsum_(i0 | inordf to_nat i0 == i) INR (to_nat i0) * P i0 =
              \rsum_(i0 |  to_nat i0 == i) INR (to_nat i0) * P i0); last first. 
  by apply:eq_bigl=> i0; rewrite inordf_eq.
apply:congr_big=> [//| x | i0]; last by move/eqP->.
rewrite /= inE.
apply:esym; apply/eqP.
case (bool_dec (to_nat x == i) true); first by move/eqP=>eqi; rewrite eqi eq_refl.
move/not_true_is_false=>noti. 
rewrite noti.
apply:not_INR.
by move/eqP:noti.
Qed.

Definition HN := 
- \rsum_(0 <= i < (\max_(a| a \in A) to_nat a).+1) Pr[X = (INR i)] * log Pr[X = (INR i)].

Hypothesis X_pos: forall a, 0 < X a.

Lemma big_eq_iota_0_1 f: \rsum_(0 <= i < (\max_(a| a \in A) to_nat a).+1) Pr[X = (INR i)] * f i=
 \rsum_(1 <= i < (\max_(a| a \in A) to_nat a).+1) Pr[X = (INR i)] * f i.
Proof.
rewrite big_ltn; last by move/card_gt0P:(dist_support_not_empty P)=>[? _]; apply:ltn0Sn.
rewrite (_: Pr[X = (INR 0)] = 0); first by rewrite mul0R add0R.
apply:esym; apply:Req_0_rmul=> i.
rewrite inE; move/eqP=> Xi_0.
by move/Rlt_not_eq:(X_pos i); rewrite Xi_0.
Qed.

Lemma Ex_nat_Xpos : \rsum_(0 <= i < (\max_(a| a \in A) to_nat a).+1) (INR i) * Pr[X = (INR i)]=
 \rsum_(1 <= i < (\max_(a| a \in A) to_nat a).+1) (INR i) * Pr[X = (INR i)].
Proof.
rewrite big_ltn; first by rewrite mul0R add0R.
by move/card_gt0P:(dist_support_not_empty P)=>[? _]; apply:ltn0Sn.
Qed.

Lemma Ex1_cond a : `E X = 1 -> (a \in [set x | P x != 0] ->  X a = 1) /\ 
(X a <> 1 -> P a = 0).
Proof.
rewrite /Ex_alt /= -{1}(pmf1 P)=>Ex1.
have inA: forall i : A, i \in A -> P i <= INR (to_nat i) * P i.
  move=> i _; rewrite -{1}(mul1R ( P i)). 
  apply:Rmult_le_compat_r; first apply:Rle0f.
  rewrite (_ : 1 = INR 1) //.
  move: (X_pos i); rewrite /= (_ : 0 = INR 0) //.
  by move/INR_lt/lt_le_S => ?; apply:le_INR.
move/(Rle_big_eq _ _ _ _ inA):Ex1=>tonat_p.
rewrite inE.
apply:conj; first by move/eqP; apply:(Rmult_eq_reg_r (P a)); rewrite mul1R (tonat_p a).
case (Req_dec (P a) 0)=>//.
have: INR (to_nat a) * P a = P a by rewrite (tonat_p a).
rewrite -{2}(mul1R (P a)).
by move/Rmult_eq_reg_r=>tmp; move/tmp.
Qed.

Lemma HN_0 : `E X = 1 -> HN = 0.
Proof.
move/Ex1_cond=> Ex1_cond.
rewrite /HN Ropp_eq_0_compat //.
rewrite {2}(_ : 0 =  \rsum_(i<-index_iota 0 (\max_(a in A) to_nat a).+1) 0); last first.
  by rewrite big_mkord; apply:Req_0_rmul.
apply:eq_bigr=> i _; rewrite /@pr /Pr /=.
case (Req_dec (INR i) 1)=>[ -> | neq0].
  have ->: \rsum_(a | a \in [set x | INR (to_nat x) == 1]) P a = 1.
    rewrite -{2}(pmf1 P).
    rewrite [in RHS](bigID (fun a => a \in[set x | INR (to_nat x) == 1])) /=.
    have <-: 0 = \rsum_(i0 | i0 \notin [set x | INR (to_nat x) == 1]) P i0.
      apply:Req_0_rmul=>i0.
      rewrite inE; move/eqP.
      by move:(Ex1_cond i0)=>[_ P0]; move/P0.
    by rewrite addR0.
  by rewrite log_1 mulR0.
have <-: 0 = \rsum_(a | a \in [set x | INR (to_nat x) == INR i]) P a.
  apply:Req_0_rmul=>i0.
  rewrite inE; move/eqP=>eq_tonat_i.
  move:neq0; rewrite -eq_tonat_i.
  by move: (Ex1_cond i0)=>[_ P0]; move/P0.
by rewrite mul0R.
Qed.

Lemma le_1_Ex : 1 <= `E X .
Proof.
rewrite/Ex_alt -(pmf1 P) /=.
apply:Rle_big_P_f_g=>i _.
rewrite -{1}(mul1R ( P i)). 
apply:Rmult_le_compat_r; first apply:Rle0f.
rewrite (_ : 1 = INR 1) //.
move: (X_pos i).
rewrite /= (_ : 0 = INR 0)//.
move/INR_lt/lt_le_S => ?.
by apply:le_INR.
Qed.

Lemma le_HN_logE_loge' : 
  HN <= `E X * log (`E X) - (`E X - 1) * log((`E X) -1).
Proof.
pose alp := (`E X - 1) / `E X.
have Ex_non0: `E X <> 0.
  apply:nesym; apply:Rlt_not_eq.
  by apply:(Rlt_le_trans _ _ _ Rlt_0_1 le_1_Ex).
move/Rle_lt_or_eq_dec:le_1_Ex=>[?| eq]; last first.
  rewrite -eq /Rminus Rplus_opp_r mul0R Ropp_0 addR0 mul1R log_1.
  move/esym/HN_0:eq->; by apply:Rle_refl.
have EX_1 : 0 < `E X - 1.
  apply:(Rplus_lt_reg_r 1).
  by rewrite addR0 addRC -addRA Rplus_opp_l addR0.
have le_alp_1 : alp < 1.
    apply:(Rmult_lt_reg_r (`E X)); first by apply:(Rlt_trans _ _ _ (Rlt_0_1)).
    rewrite /alp mul1R -mulRA -Rinv_l_sym // mulR1.
    by apply:Rgt_lt; apply:(tech_Rgt_minus _ _ (Rlt_0_1)).
have lt_0_alp : 0 < alp.
  rewrite /alp.
  apply:Rlt_mult_inv_pos=>//.
  by apply:(Rle_lt_trans _ _ _ (Rle_0_1)).
rewrite [X in _ <= X](_ :_ = log ( alp / (1 - alp)) - (log alp) * `E X); last first.
  rewrite (_ :alp / (1 - alp) = `E X - 1); last first.
    rewrite /alp (_: (1 - ( (`E X - 1) / `E X)) = / `E X).
      by rewrite /Rdiv Rinv_involutive // -mulRA -Rinv_l_sym // mulR1.
    rewrite /Rdiv Rmult_minus_distr_r -Rinv_r_sym // mul1R /Rminus Ropp_minus_distr.
    by rewrite addRC -addRA Rplus_opp_l addR0.
  rewrite /Rdiv !log_mult //; last by apply:Rinv_0_lt_compat;apply:(Rlt_trans _ _ _ (Rlt_0_1)).
    rewrite log_Rinv //; last by apply:(Rlt_trans _ _ _ (Rlt_0_1)).
    rewrite {1 2}/Rminus {1}Rmult_plus_distr_r Ropp_plus_distr addRA.
    rewrite -Ropp_mult_distr_l_reverse -Ropp_mult_distr_l_reverse Ropp_involutive mul1R addRC. 
    apply:Rplus_eq_compat_l.
    rewrite [in RHS]mulRC Rmult_plus_distr_l addRC  Ropp_plus_distr.
    by rewrite Ropp_mult_distr_r_reverse Ropp_mult_distr_l_reverse Ropp_involutive.
apply:(Rle_trans _  (log (alp * (1 - (alp ^ (\max_(a| a \in A) to_nat a))) / (1 - alp))
                     - log alp * `E X) _); last first.
  apply:Rplus_le_compat_r.
  apply:log_increasing_le.
    apply:Rmult_lt_0_compat.
      apply:Rmult_lt_0_compat=> //. 
      apply:Rgt_lt; apply:Rgt_minus; apply:Rlt_gt.
      have: (0 < \max_(a in A) to_nat a)%coq_nat.
        apply:ltP.
        move/card_gt0P:(dist_support_not_empty P)=>[a _].
        apply:(bigmax_sup a)=> //.
        by move:(X_pos a); rewrite /X /= (_ : 0 = INR 0)//;move/INR_lt/ltP.      
      have: 0 <= alp < 1 by apply:conj=> //; first apply:Rlt_le.
      move/(pow_lt_1_compat _ ((\max_(a in A) to_nat a)))=>tmp; move/tmp.
      by move/proj2.
    by apply:Rinv_0_lt_compat; apply:Rgt_lt; apply:Rgt_minus; apply:Rlt_gt.
  rewrite /Rdiv -mulRA.
  apply:Rmult_le_compat_l; first by apply:Rlt_le.
  rewrite -{2}(mul1R (/ (1 - alp))) ; apply:Rmult_le_compat_r.
    by apply:Rlt_le; apply:Rinv_0_lt_compat; apply:Rgt_lt; apply:Rgt_minus; apply:Rlt_gt.
  rewrite -{2}(addR0 1) /Rminus; apply:Rplus_le_compat; first exact:Rle_refl.
  apply:Rge_le; apply:Ropp_0_le_ge_contravar.
  by apply:pow_le; apply:Rlt_le.
rewrite -big_pow1; last by apply:Rlt_not_eq.
rewrite Ex_nat. 
rewrite mulRC (big_morph _ (morph_mulRDl _) (mul0R _)).
apply:(Rplus_le_reg_r (\rsum_(i<-index_iota 0 (\max_(a in A) to_nat a).+1)
      INR i * Pr[X = (INR i)] * log alp)).
rewrite -addRA Rplus_opp_l addR0.
rewrite [X in _ + X <= _](_ : _ = \rsum_(i<-index_iota 0 (\max_(a in A) to_nat a).+1)
                                    Pr[X = (INR i)] * log (alp ^ i)); last first.
  by apply:eq_bigr=>?;rewrite log_pow // [in RHS]mulRC -mulRA (mulRC _ (log alp)) mulRA.
rewrite /HN addRC; move:Ropp_minus_distr; rewrite/Rminus; move<-.
rewrite -(Ropp_involutive (log (\rsum_(i<-index_iota 1 (\max_(a in A) to_nat a).+1) alp ^ i))).
apply:Ropp_le_contravar; apply:Rge_le.
rewrite (big_morph _ morph_Ropp Ropp_0).
rewrite -big_split /=.
rewrite [X in X >= _](_ : _ =  \rsum_(i<-index_iota 0 (\max_(a in A) to_nat a).+1)
      Pr[X = (INR i)] * (log Pr[X = (INR i)] - log (alp ^ i))); last first.
  by apply:eq_bigr=>i _; rewrite Rmult_plus_distr_l Ropp_mult_distr_r_reverse.
rewrite big_eq_iota_0_1.
rewrite[X in _ >= X](_ : _ =  1 * (0 -
               log (\rsum_(i<-index_iota 1 (\max_(a in A) to_nat a).+1) alp ^ i))); last first.
  by rewrite mul1R Rminus_0_l.
have pmf1': \rsum_(i<-index_iota 1 (\max_(a in A) to_nat a).+1) Pr[X = (INR i)] = 1.
  rewrite -dist_nat.
  rewrite [in RHS]big_ltn.
    rewrite (_: Pr[X = (INR 0)] = 0); first by rewrite add0R.
    apply:esym; apply:Req_0_rmul=> i.
    rewrite inE; move/eqP=> Xi_0.
    by move/Rlt_not_eq:(X_pos i); rewrite Xi_0.
  move/card_gt0P:(dist_support_not_empty P)=>[a _].
  by apply:ltn0Sn.
rewrite -{2}log_1 -pmf1'.
have Rle0f' i:0 <= Pr[X = (INR i)] by apply:Rle_big_0_P_g=>? _;  apply:(Rle0f P).
have Rle0g i:0 <= alp ^ i by apply:pow_le; apply:Rlt_le.
pose f := mkPosFun Rle0f'.
pose g := mkPosFun Rle0g.
have dom_by_fg:  f <<  g.
  move=> i; move/pow0_inv=>alp0.
  by move:lt_0_alp; rewrite alp0;move/Rlt_not_eq.
have le_1_maxn : (leq 1 (\max_(a in A) to_nat a).+1)%N by apply:ltn0Sn.
by apply:(log_sum_inequality_nat dom_by_fg le_1_maxn).
Qed.

Lemma le_HN_logE_loge : HN <= log (`E X) + log (exp 1).
Proof.
move/Rle_lt_or_eq_dec:le_1_Ex=>[? | eq_Ex_1]; last first.
  rewrite -eq_Ex_1 log_1 add0R.
  by move/esym/HN_0:eq_Ex_1->; apply:log_exp1_Rle_0.
have Ex_non0: `E X <> 0.
  apply:nesym; apply:Rlt_not_eq.
  by apply:(Rlt_le_trans _ _ _ Rlt_0_1 le_1_Ex).
have Ex_1 : 0 < `E X - 1.
  apply:(Rplus_lt_reg_r 1).
  by rewrite addR0 addRC -addRA Rplus_opp_l addR0.
have neq_Ex1_0 :(`E X + -1) <> 0.
  by apply:nesym; apply:Rlt_not_eq.
apply:(Rle_trans _ (`E X * log (`E X) - (`E X - 1) * log((`E X) -1)) _).
  by apply:le_HN_logE_loge'.
rewrite {1}(_ :`E X = (1 + (`E X - 1))); last by rewrite /Rminus addRC -addRA Rplus_opp_l addR0.
rewrite [X in X <= _](_ : _ = log (`E X) + (`E X - 1) * log (`E X) - (`E X - 1) * log (`E X - 1)); last first.
  rewrite /Rminus addRC [in RHS]addRC; apply:Rplus_eq_compat_l.
  by rewrite Rmult_plus_distr_r mul1R.
rewrite /Rminus -addRA; apply:Rplus_le_compat_l.
rewrite [X in X <= _](_ : _ = (`E X + -1) * 
                                           (log (`E X) - log (`E X + -1))); last first.
  by rewrite Rmult_plus_distr_l Ropp_mult_distr_r_reverse.
have y_minus_x: `E X - (`E X + -1) = 1.
  by rewrite /Rminus Ropp_plus_distr Ropp_involutive (addRC _ 1) addRC -addRA Rplus_opp_l addR0.
rewrite -(mul1R (log (exp 1))).
rewrite -{3}y_minus_x.
apply:div_diff_ub=>//; first by apply:Rlt_le.
  by apply:Rlt_le; apply:(Rlt_trans _ _ _ (Rlt_0_1)).
Qed.
