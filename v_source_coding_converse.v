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
move=> X convex.
rewrite/Ex_alt/index_enum.
move:(enum_uniq A) X (pmf1 (rv_dist X)).
rewrite enumT /Ex_alt /index_enum.
elim:(Finite.enum _) => [_ X | hd tl IH].
  rewrite big_nil=> H.
  by move:R1_neq_R0; rewrite H.
case/andP=>a_not l_uniq X. 
rewrite !big_cons inE.
move/(Rplus_eq_compat_l (- `p_ X hd)).
rewrite addRA Rplus_opp_l add0R addRC.

case: (Req_dec (1- `p_ X hd) 0) => [| neq_dist_1].
  move/Rminus_diag_uniq=> dist1.
  rewrite dist1 Rplus_opp_r.
  move/eqP; rewrite eq_sym; move/eqP.
  rewrite big_uniq//.
  move/(Req_0_rmul_inv _ _ (Rle0f `p_ X))=> intl_p0.
  have gp_0: forall g, 0 = \big[Rplus/0]_(j <- tl | j \in A) (g j * `p_ X j).
    move=>g.
    rewrite big_uniq //.
    by apply:Req_0_rmul=>i ?; rewrite -(intl_p0 i) // mulR0.
  rewrite -!gp_0 !addR0 -dist1 !mulR1.
  by apply: Rle_refl. 

have leq_dist_1: 0 < (1 + - `p_ X hd).
  apply:(Rplus_gt_reg_l (`p_ X hd)).
  rewrite addRC -addRA Rplus_opp_l !addR0.
  apply:Rlt_gt.
  move:(dist_max `p_ X hd) neq_dist_1.
  case=>//.
  by move->; rewrite /Rminus Rplus_opp_r.

move/(Rmult_eq_compat_r (/(1 + - `p_ X hd))).
rewrite !(big_morph _ (morph_mulRDl _) (mul0R _)).
rewrite -(Rinv_r_sym (1 + - `p_ X hd) neq_dist_1)=> Hpmf1.
rewrite -(mulR1 (\big[Rplus/0]_(j <- tl | j \in A) (X j * `p_ X j))). 
rewrite (Rinv_r_sym (1 - `p_ X hd) neq_dist_1).
rewrite (addRC (X hd * _) _) (addRC (f (X hd) * _) _).
rewrite mulRC -mulRA addRC mulRC.
(*  set t := `p_ X hd.
    set y := (/(1 - t) *\big[Rplus/0]_(j <- tl | j \in A) (X j * `p_ X j)).
    set x := (X hd).*)
apply:(Rle_trans _ ((`p_ X hd) * f (X hd) + (1 - `p_ X hd) * 
                  f ((/ (1 - `p_ X hd) * \big[Rplus/0]_(j <- tl | j \in A) (X j * `p_ X j))))).
  by apply: (convex _ _ _  (conj ((Rle0f (`p_ X) hd)) (dist_max (`p_ X) hd))).
rewrite mulRC addRC mulRC.
apply:Rplus_le_compat_r.

apply:(Rmult_le_reg_r (/(1 + - `p_ X hd))).
  apply:(Rmult_lt_reg_r (1 + - `p_ X hd) _ _ leq_dist_1).
  by rewrite mul0R -Rinv_l_sym; [apply:Rlt_0_1 | apply:neq_dist_1].
rewrite -mulRA -Rinv_r_sym; last by apply:neq_dist_1.
rewrite mulR1 mulRC.
rewrite !(big_morph _ (morph_mulRDl _) (mul0R _)).

have H: \big[Rplus/0]_(j <- tl | j \in A) (`p_ X j * / (1 + - `p_ X hd)) =
     \big[Rplus/0]_(j <- tl | j \in A) (if j \in tl then `p_ X j * / (1 + - `p_ X hd) else 0).
  rewrite big_seq_cond [in RHS]big_seq_cond.
  apply: big_ind2 => [| x1 x2 y1 y2 H4 H3 | i ]=>//.
    by rewrite H4 H3.
  by case/andP; move->.

pose pos_f' x := if (x \in tl) then (`p_ X x * / (1 + - `p_ X hd)) else 0.
have pos_f'_pos: forall x , 0 <= pos_f' x. 
  move=> x.
  rewrite/pos_f'.
  case:ifP =>[_ | _]; last by apply: Rle_refl.
  by apply:(Rle_mult_inv_pos _ _ (Rle0f (`p_ X) x)).
pose pmf' := mkPosFun pos_f'_pos.
have pmf1': \big[Rplus/0]_(j| j \in A ) pmf' j = 1.
  rewrite -Hpmf1 H (bigID (fun x => x \in tl)) /= /pos_f' (big_uniq _ l_uniq) /=.
  rewrite -{2}(Rplus_0_r (\rsum_(i | i \in tl) _)).
  apply: Rplus_eq_compat_l.
  apply:esym; apply/Req_0_rmul => i.
  by move/negb_true_iff ->. 
pose dist' := mkDist pmf1'.
pose rvar' := mkRvar  dist' (rv_fun X).
have H1: forall f, \big[Rplus/0]_(j <- tl | j \in A) (f (X j) * `p_ X j * / (1 + - `p_ X hd)) = 
       \big[Rplus/0]_(j <- tl | j \in A) (f (rvar' j) * (`p_ rvar' j )).
  move=> f0.
  rewrite big_seq_cond [in RHS]big_seq_cond.
  apply:eq_bigr => i.
  case/andP=>inl _.
  by rewrite /= /pos_f' inl mulRA.
rewrite H1 (H1 (fun x => x)); apply:(IH l_uniq).
by rewrite /= /pos_f' -{2}Hpmf1 H.
Qed.

End Jensen.

Section logsum.
Variable A : finType.

Lemma Rlt_big_0_posf: forall f : A -> R+, (exists a, 0 < f a) -> 0 < \rsum_(i | i \in A) f i.
Proof.
move=>f; case=> a fa_pos.
rewrite big_seq -big_seq /index_enum.
rewrite (bigD1_seq a) // /=; last by rewrite -enumT; move:(enum_uniq A).
apply: (Rplus_lt_le_0_compat _ _ fa_pos).
apply: Rle_big_0_P_g; by move: (Rle0f f).
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
apply: (Rmult_le_reg_r (\rsum_(i | i \in A) g i) _ _ lt_big_0).
rewrite mul0R (big_morph _ (morph_mulRDl _) (mul0R _)). 
rewrite [X in X <= 0](_ : _ = \rsum_(i | i \in A)
                               f i * (\rsum_(i0 | i0 \in A) g i0) *
                              (log (g i * (\rsum_(i0 | i0 \in A) f i0)) -
                               log (f i * (\rsum_(i0 | i0 \in A) g i0)))); last first.
  apply:eq_bigr=> i _.
  by rewrite -!mulRA;  apply: Rmult_eq_compat_l; rewrite mulRC.
apply:(Rle_trans _ ((\rsum_(i | i \in A) ((g i * (\rsum_(i0 | i0 \in A) f i0) - 
                                       (f i * (\rsum_(i0 | i0 \in A) g i0))))) * log (exp 1))).
  rewrite (big_morph _ (morph_mulRDl _) (mul0R _)).
  apply:Rle_big_P_f_g => a _; apply: div_diff_ub.
      by move: lt_big_0; move/Rlt_le=>?; apply: (Rmult_le_pos _ _ (Rle0f f a) _).
    have le_bigf_0: (0 <= \rsum_(i | i \in A) f i) by apply: Rle_big_0_P_g; move: (Rle0f f).
    by apply:(Rmult_le_pos _ _ (Rle0f g a) le_bigf_0).
  case/Rmult_integral=> [ /f_dom_by_g -> |le_0_sum]; first by rewrite mul0R.
(*  suff -> : f a = 0 by rewrite mul0R.*)
  rewrite (_: f a = 0); first by rewrite mul0R.
  apply:esym; move/esym:le_0_sum=> eq_0_sum.
  by apply:(Req_0_rmul_inv _ f (Rle0f f) eq_0_sum).
rewrite -{4}(mul0R (log (exp 1))); apply:Rmult_le_compat_r; first by apply:log_exp1_Rle_0.
rewrite big_split /=.
rewrite -(big_morph _ morph_Ropp Ropp_0) -!(big_morph _ (morph_mulRDl _) (mul0R _)).
rewrite mulRC Rplus_opp_r; by apply:Rle_refl.
Qed.

End logsum.

Section logsum_n.


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
  apply: eq_big_nat=> i i_in.
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
  move:eq_big_0.
  move/(Req_0_rmul_inv _ _ Rle0g)=> gi_0.
  have: g (addn i m)%N = 0 by rewrite (gi_0 i).
  by move/f_dom_by_g->; rewrite mul0R.
apply:(Rmult_le_reg_r (\rsum_(i<-index_iota m n) g i) _ _ lt_big_0).
rewrite mul0R (big_morph _ (morph_mulRDl _) (mul0R _)). 
rewrite [X in X <= 0](_ : _ = \rsum_(m <= j < n)
                               f j * (\rsum_(m <= k < n) g k) *
                              (log (g j * (\rsum_(m <= k < n) f k)) -
                               log (f j * (\rsum_(m <= k < n) g k)))); last first.
  apply:eq_bigr=> i _.
  by rewrite -!mulRA;  apply: Rmult_eq_compat_l; rewrite mulRC.
apply:(Rle_trans _ ((\rsum_(m <= j < n) ((g j * (\rsum_(m <= k < n) f k) - 
                                       (f j * (\rsum_(m <= k < n) g k))))) * log (exp 1))).
  rewrite (big_morph _ (morph_mulRDl _) (mul0R _)) -(add0n m) !big_addn !big_mkord.
  move:lt_big_0; rewrite -(add0n m) big_addn big_mkord => le_big_0.
  apply:Rle_big_P_f_g => a _; apply: div_diff_ub.
  apply:Rmult_le_pos; first by apply:(Rle0f f).
  by apply: Rle_big_0_P_g; move: (Rle0f g).
    have le_bigf_0: (0 <= \rsum_(i<n - (0 + m)) f (addn i (0 + m))) by apply: Rle_big_0_P_g; move: (Rle0f f).
    apply:Rmult_le_pos=> //;first by apply (Rle0f g).
  case/Rmult_integral=> [ /f_dom_by_g -> |le_0_sum]; first by rewrite mul0R.
(*  suff -> : f a = 0 by rewrite mul0R.*)
  rewrite (_: f (addn a (0 + m)) = 0); first by rewrite mul0R.
  apply:esym; move/esym:le_0_sum=> eq_0_sum.
  have Rle0f': forall x: ordinal_finType (n - m), 0 <= f (addn (@nat_of_ord _ x) m)%N.
    by move=> x; apply:(Rle0f f).
  by apply:(Req_0_rmul_inv _ _  Rle0f' eq_0_sum).
rewrite -{4}(mul0R (log (exp 1))); apply:Rmult_le_compat_r; first by apply:log_exp1_Rle_0.
rewrite big_split /=.
rewrite -(big_morph _ morph_Ropp Ropp_0) -!(big_morph _ (morph_mulRDl _) (mul0R _)).
rewrite mulRC Rplus_opp_r; by apply:Rle_refl.
Qed.
End logsum_n.

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

Variable n m: nat.
Variable x : R.
Hypothesis le_m_n : (leq m n)%N.
Hypothesis neq_x_1 : x <> 1.
(* (n0 <= i < n に拡張？) *)

Lemma big_pow : \rsum_(m <= i < n.+1) x ^ i =  x ^ m * (1 - (x ^ n.+1)) / (1 - x).
Proof.
move/nesym /Rminus_eq_contra:neq_x_1=> ?.
elim n=> [|n' IH].
  by rewrite /Rminus /Rdiv pow_1 big_nat1 pow_O -Rinv_r_sym.
rewrite big_nat_recr /= IH.
apply (Rmult_eq_reg_r (1 - x)); last by[].
rewrite Rmult_plus_distr_r.
rewrite /Rdiv -mulRA -[in RHS]mulRA -!Rinv_l_sym; last by[].
rewrite !mulR1.
rewrite Rmult_plus_distr_l mulR1.
rewrite addRA /Rminus.
rewrite -(addRA 1 (- x ^ n'.+1) _) Rplus_opp_l addR0 mulRC.
by rewrite Ropp_mult_distr_l_reverse.
Qed.

Lemma big_pow1 : \rsum_(1 <= i < n.+1) x ^ i = x * (1 - (x ^ n)) / (1 - x).
Proof.
move/nesym /Rminus_eq_contra:neq_x_1=> ?.
elim n=> [|n' IH].
  by rewrite big_nil/= /Rminus Rplus_opp_r mulRC /Rdiv -mulRA mul0R.
rewrite big_add1 big_nat_recr /=.
rewrite (_ : \rsum_(i<-index_iota 0 n') x * x ^ i = \rsum_(i<-index_iota 0 (n'.+1).-1) x ^ i.+1) //.
rewrite (_ :  \rsum_(i<-index_iota 0 n'.+1.-1) x ^ i.+1 =  \rsum_(i<-index_iota 1 n'.+1) x ^ i); last by rewrite big_add1.
rewrite IH.
apply (Rmult_eq_reg_r (1 - x));last by[].
rewrite Rmult_plus_distr_r.
rewrite /Rdiv -mulRA -[in RHS]mulRA -!Rinv_l_sym; last by[].
rewrite !mulR1 !tech_pow_Rmult.
rewrite !Rmult_plus_distr_l -addRA !mulR1.
apply Rplus_eq_compat_l.
by rewrite !Ropp_mult_distr_r_reverse !tech_pow_Rmult addRA Rplus_opp_l add0R mulRC tech_pow_Rmult.
Qed.

Lemma log_pow r: 0 < r -> log (r ^ n) = (INR n) * log r.
Proof.
elim:n=> [|n' IH lt_0_r]; first by rewrite log_1 mul0R.
rewrite log_mult//;first by rewrite IH // -addn1 addRC plus_INR Rmult_plus_distr_r mul1R.
by apply:pow_lt.
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
            (fun i => i \in 'I_(\max_(a | a \in A) to_nat a).+1)) /=; last by[].
pose n1 := (\max_(a in A) to_nat a).
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
            (fun i => i \in 'I_(\max_(a | a \in A) to_nat a).+1)) /=; last done.
set n1 := (\max_(a in A) to_nat a).
rewrite (_ : \rsum_(0 <= i < n1.+1) INR i * Pr[X = (INR i)] = 
             \rsum_(i | i \in 'I_n1.+1) INR i * Pr[X = (INR i)]); last first.
  rewrite /index_iota subn0 -val_enum_ord.
  rewrite big_map.
  rewrite big_uniq /=; last apply enum_uniq.
  by apply eq_bigl=> i; first rewrite /= mem_enum.
apply eq_bigr=> i H.
rewrite /@pr /Pr.
rewrite mulRC (big_morph _ (morph_mulRDl _) (mul0R _)).
rewrite (_ : \rsum_(i0 | i0 \in _) `p_ X i0 * INR i =
    \rsum_(i0 | i0 \in [set x | X x == INR i]) INR i * `p_ X i0); last by apply eq_bigr=> a _; rewrite mulRC.
rewrite ( _ : \rsum_(i0 | inordf to_nat i0 == i) INR (to_nat i0) * P i0 =
 \rsum_(i0 |  to_nat i0 == i) INR (to_nat i0) * P i0); last by apply eq_bigl=> i0; rewrite inordf_eq.
apply congr_big=> [//| x | i0].
rewrite /= inE.
apply:esym.
apply/eqP.
case (bool_dec (to_nat x == i) true); first by move/eqP=>eqi; rewrite eqi eq_refl.
move/not_true_is_false=> neqi. 
rewrite neqi.
apply not_INR.
move: neqi.
by move/eqP.
by move/eqP->.
Qed.

Definition HN := 
- \rsum_(0 <= i < (\max_(a| a \in A) to_nat a).+1) Pr[X = (INR i)] * log Pr[X = (INR i)].

Hypothesis X_pos: forall a, 0 < X a.

Lemma big_eq_iota0_1 f: \rsum_(0 <= i < (\max_(a| a \in A) to_nat a).+1) Pr[X = (INR i)] * f i=
 \rsum_(1 <= i < (\max_(a| a \in A) to_nat a).+1) Pr[X = (INR i)] * f i.
Proof.
rewrite big_ltn.
rewrite (_: Pr[X = (INR 0)] = 0); first by rewrite mul0R add0R.
apply:esym; apply:Req_0_rmul=> i.
rewrite inE; move/eqP=> Xi_0.
by move/Rlt_not_eq:(X_pos i); rewrite Xi_0.
move/card_gt0P:(dist_support_not_empty P)=>[a _].
by apply:ltn0Sn.
Qed.

Lemma Ex_nat_Xpos : \rsum_(0 <= i < (\max_(a| a \in A) to_nat a).+1) (INR i) * Pr[X = (INR i)]=
 \rsum_(1 <= i < (\max_(a| a \in A) to_nat a).+1) (INR i) * Pr[X = (INR i)].
Proof.
rewrite big_ltn; first by rewrite mul0R add0R.
move/card_gt0P:(dist_support_not_empty P)=>[a _].
by apply:ltn0Sn.
Qed.

Lemma Ex_1 a : `E X = 1 -> (a \in [set x | P x != 0] ->  X a = 1) /\ 
(X a <> 1 -> P a = 0).
Proof.
rewrite /Ex_alt /=.
rewrite -{1}(pmf1 P).
have H : forall i : A, i \in A -> P i <= INR (to_nat i) * P i.
  move=> i _.
  rewrite -{1}(mul1R ( P i)). 
  apply Rmult_le_compat_r; first apply Rle0f.
  rewrite (_ : 1 = INR 1); last done.
  move: (X_pos i).
  rewrite /= (_ : 0 = INR 0); last by[].
  by move/INR_lt/lt_le_S => ?; apply:le_INR.
move/Rle_big_eq.
move=> H1 .
apply H1 with a in H; last done.
rewrite inE.
split.
move/eqP.
apply (Rmult_eq_reg_r (P a)).
by rewrite mul1R.
case (Req_dec (P a) 0); first done.
move:H.
rewrite -{2}(mul1R (P a)).
move/Rmult_eq_reg_r=> H.
by move/H.
Qed.

Lemma HN_0 : `E X = 1 -> HN = 0.
Proof.
move/Ex_1=> Ex_1.
rewrite /HN Ropp_eq_0_compat; first by [].
rewrite {2}(_ : 0 =  \rsum_(i<-index_iota 0 (\max_(a in A) to_nat a).+1) 0); last first.
  by rewrite big_mkord; apply Req_0_rmul=> i _.
apply:eq_bigr=> i _.
rewrite /@pr /Pr /=.
case (Req_dec (INR i) 1)=>[ -> | neq0].
have : \rsum_(a | a \in [set x | INR (to_nat x) == 1]) P a = 1.
rewrite -{2}(pmf1 P).
rewrite [in RHS](bigID (fun a => a \in[set x | INR (to_nat x) == 1])) /=.
have : 0 = \rsum_(i0 | i0 \notin [set x | INR (to_nat x) == 1]) P i0 .
apply Req_0_rmul=>i0.
rewrite inE.
move/eqP.
move:(Ex_1  i0)=>[_ P0].
by move/P0->.
by move<-; rewrite addR0.
move->.
by rewrite log_1 mulR0.
have : 0 = \rsum_(a | a \in [set x | INR (to_nat x) == INR i]) P a.
apply Req_0_rmul=>i0.
rewrite inE.
move/eqP=> i0i.
rewrite -i0i in neq0.
move: (Ex_1 i0)=>[_ P0].
by apply P0 in neq0. 
move<-.
by rewrite mul0R.
Qed.

Lemma le_1_Ex : 1 <= `E X .
Proof.
rewrite /Ex_alt -(pmf1 P) /=.
apply Rle_big_P_f_g=>i _.
rewrite -{1}(mul1R ( P i)). 
apply Rmult_le_compat_r; first apply Rle0f.
rewrite (_ : 1 = INR 1); last done.
move: (X_pos i).
rewrite /= (_ : 0 = INR 0); last done.
move/INR_lt.
move/lt_le_S => Xi_pos.
by apply le_INR.
Qed.

Lemma converse_ : 
  HN <= `E X * log (`E X) - (`E X - 1) * log((`E X) -1).
Proof.
pose alp := (`E X - 1) / `E X.
have Ex_non0: `E X <> 0.
  apply:nesym; apply:Rlt_not_eq.
  by apply:(Rlt_le_trans _ _ _ Rlt_0_1 le_1_Ex).
move/Rle_lt_or_eq_dec:le_1_Ex=>[less | eq]; last first.
  rewrite -eq /Rminus Rplus_opp_r mul0R Ropp_0 addR0 mul1R log_1.
  move/esym/HN_0:eq->; by apply Rle_refl.
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
      apply pow_lt_1_compat.
        apply:conj=> //; first by apply:Rlt_le.
      apply:ltP. 
      move/card_gt0P:(dist_support_not_empty P)=>[a _].
      apply:(bigmax_sup a)=> //.
      by move:(X_pos a); rewrite /X /= (_ : 0 = INR 0)//;move/INR_lt/ltP.
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
rewrite big_eq_iota0_1.
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


  forall (x : R) (n : nat), 0 <= x < 1 -> (0 < n)%coq_nat -> 0 <= x ^ n < 1
Rlt_pow:
  forall (x : R) (n m : nat), 1 < x -> (n < m)%coq_nat -> x ^ n < x ^ m
Rlt_minus: forall r1 r2 : R, r1 < r2 -> r1 - r2 < 0

log  - log alp * `E X
Ropp_plus_distr
Ropp_minus_distr

 r. add
move/nesym/Rdichotomy:Ex_non0.  move/nesym:Ex_non0.
 ; last first.
    

alp * `E X + log (exp2 (- alp)) - log (1 - (exp2 (- alp)))); last first.






pose alp := log(`E X) - log(`E X -1).
move: le_1_Ex.
move/Rle_lt_or_eq_dec=>[less | eq]; last first.
  rewrite -eq /Rminus Rplus_opp_r mul0R Ropp_0 addR0 mul1R log_1.
  have :  `E X = 1 by rewrite eq.
  move/HN_0 => ->; by apply Rle_refl.
have EX_1 : 0 < `E X - 1.
  apply (Rplus_lt_reg_r 1).
  by rewrite addR0 addRC -addRA Rplus_opp_l addR0.
have alppos : 0 < alp.
  rewrite /alp.
  apply (Rplus_lt_reg_r (log (`E X - 1))).
  rewrite addR0 addRC -addRA Rplus_opp_l addR0.
  apply log_increasing=> //.
  apply Rgt_lt; apply tech_Rgt_minus.
  exact: Rlt_zero_1.
rewrite [X in _ <= X](_ :_ = alp * `E X + log (exp2 (- alp)) - log (1 - (exp2 (- alp)))); last first.
  rewrite log_exp2 /alp.
  rewrite Ropp_minus_distr.
  rewrite /Rminus exp2_plus exp2_log //.
  rewrite (_ : - log (1 + - ((`E X + -1) * exp2 (- log (`E X)))) = log (`E X)); last first.
  rewrite -{2}(Ropp_involutive (log (`E X))).
  apply Ropp_eq_compat.
  rewrite -log_Rinv; last exact: Ex_pos.
  rewrite exp2_log; last by apply Rinv_0_lt_compat; apply Ex_pos.
  rewrite -{1}(Rinv_r (`E X)); last first.
    move: Ex_pos.
    move/Rlt_gt.
    by move/Rgt_not_eq.
    rewrite -Ropp_mult_distr_l_reverse.
    by rewrite -Rmult_plus_distr_r Ropp_plus_distr addRA Rplus_opp_r add0R Ropp_involutive mul1R.
  rewrite -addRA -addRA Rplus_opp_l addR0.
  rewrite !Rmult_plus_distr_r mulRC -addRA.
  apply Rplus_eq_compat_l.
  rewrite Ropp_plus_distr mulRC Ropp_mult_distr_l_reverse -Ropp_mult_distr_l_reverse .
  by rewrite mul1R Ropp_involutive.
apply (Rplus_le_reg_r (- alp * `E X)).
apply Ropp_le_cancel. 
rewrite addRC addRA addRA Ropp_plus_distr Ropp_plus_distr. 
rewrite  Ropp_plus_distr Ropp_mult_distr_l_reverse !Ropp_involutive Rplus_opp_r add0R addRC.
rewrite Ropp_plus_distr Ropp_involutive.
rewrite -log_Rinv; last by apply exp2_pos.
have help: 0 < 1 - exp2 (- alp).
  apply (Rplus_lt_reg_r (exp2 (- alp))).
  rewrite addR0 addRC -addRA Rplus_opp_l addR0.
  rewrite -(exp2_log Rlt_zero_1) log_1.
  apply exp2_increasing.
  by apply Ropp_lt_gt_0_contravar.
rewrite -(log_mult help); last by apply Rinv_0_lt_compat; apply exp2_pos.
rewrite -[X in X <= _](Ropp_involutive).
rewrite -log_Rinv; last first.
  apply (Rmult_lt_reg_r (exp2 (- alp))); first by apply exp2_pos.
  rewrite mul0R -mulRA -Rinv_l_sym; last first.
    move: (exp2_pos (- alp)).
    move/Rlt_gt.
    by move/Rgt_not_eq.
  rewrite mulR1.
  exact: help.
rewrite mulRC Rinv_mult_distr; last first; first by apply Rgt_not_eq; apply Rlt_gt.
  apply Rgt_not_eq; apply Rlt_gt.
  by apply Rinv_0_lt_compat; apply exp2_pos.
rewrite Rinv_involutive; last by apply Rgt_not_eq; apply Rlt_gt; apply exp2_pos.


apply (Rle_trans _ (- log (\rsum_(1 <= i < (\max_(a| a \in A) to_nat a).+2) (exp2 (- alp)) ^ i))).
  apply Ropp_ge_le_contravar.
  apply Rle_ge.
  apply log_increasing_le; last first.
    by apply b_less.
  rewrite big_add1.
  rewrite big_mkord.
  apply:Rlt_big_0_g.
  rewrite /=.
  by rewrite card_ord.
  move=>?.
  apply:pow_gt0.
  by apply:exp2_pos.

rewrite/alp.
rewrite /H_N.
rewrite -Ex_Ex_alt Ex_nat.


  apply (Rle_trans _ (- log (exp2 alp / (1 - exp2 (- alp))))).
  apply Ropp_ge_le_contravar.
  apply Rle_ge.
  apply log_increasing_le.
  apply R
 0 < r ->
       \rsum_(i<-index_iota 0 (\max_(a in A) to_nat a).+1) exp2 (- r) ^ i <=
       exp2 r / (1 - exp2 (- r))
  rewrite b_sum; last by apply Rgt_not_eq; apply Rlt_gt.
  rewrite /Rdiv !log_mult.
  rewrite !Ropp_plus_distr.
  rewrite log_exp2 Ropp_involutive. 
  apply Rplus_le_compat_r.
  rewrite Ropp_plus_distr Ropp_involutive.
  rewrite exp2_plus exp2_log.
  rewrite -log_Rinv. 
  rewrite -(log_Rinv Ex_pos).
  rewrite exp2_log.
  rewrite Rmult_plus_distr_l
  rewrite -Rinv_l_sym /Rminus. 
  rewrite Ropp_plus_distr. addRA.
  
  
  rewrite  !/Rdiv Ropp_mult_distr_l_reverse.
 rewrite Ropp_mult_distr_l_reverse. log_exp2 .
  apply Rmult_le_compat_r.
((1 - ((exp2 (- alp)) ^ (\max_(a| a \in A) to_nat a).+1)) / (1 - (exp2 (- alp))))).

Rmult_plus_distr_r: forall r1 r2 r3 : R, (r1 + r2) * r3 = r1 * r3 + r2 * r3

Ropp_plus_distr: forall r1 r2 : R, - (r1 + r2) = - r1 + - r2
Ropp_mult_distr_l_reverse: forall r1 r2 : R, - r1 * r2 = - (r1 * r2)
Rmult_opp_opp: forall r1 r2 : R, - r1 * - r2 = r1 * r2
Ropp_mult_distr_r_reverse: forall r1 r2 : R, r1 * - r2 = - (r1 * r2)


Lemma b_sum r : r <> 0 -> \rsum_(0 <= i < (\max_(a| a \in A) to_nat a).+1) (exp2 (- r)) ^ i =  
                 (1 - ((exp2 (- r)) ^ (\max_(a| a \in A) to_nat a).+1)) / (1 - (exp2 (- r))).

 -mulRA.

rewrite (Rplus_opp_l (alp * `E X)).

; apply Rge_le.
  
    rewrite Ropp_inv_permute.
    rewrite log_Rinv.
  move/Rlt_not_eq. Rlt_dichotomy_converse. Rdichotomy.
  rewrite (_ : - log (`E X + -1) = log (/ (`E X + - 1))); last first.

  rewrite -(log_Rinv EX_1 (`E X + -1)).

  case: (Req_dec (`E X) 1)=>[Eeq0 |Eneq0].
  rewrite !Eeq0 log_1 mulR0 /= /Rminus Rplus_opp_r mul0R Ropp_0 add0R.
  apply HN_0 in Eeq0.
  by move:Eeq0 ->; apply Rle_refl.
rewrite [X in _ <= X](_ :_ = alp * `E X + log (exp2 alp) - log (1 - exp2 alp)); last first.
rewrite 

 rewrite 


have alp_pos: 0 < alp.
  rewrite /alp.
  apply (Rplus_lt_reg_r (log (`E X - 1))).
  rewrite addR0 addRC -addRA Rplus_opp_l addR0.
  apply log_increasing.
have : 
rewrite /H_N.


.
lt_not_eq
apply Rlt_le; apply exp_pos_pos.
apply exp_1.
apply Rle_minus.
apply pow_R1_Rle.
apply Rfourier_lt.

move => i0.
 rewrite /=.
move: (inordf_eqall _ to_nat i0) ->.
by rewrite H1.
rewrite H1 in it.

apply/eqP.
case (bool_dec (to_nat i0 == i) true).
move/eqP=> it.
rewrite it eq_refl.
rewrite inordf_eqall in it.
by apply ord_inj.
move/not_true_is_false.
move=> it. 
rewrite it.
apply/eqP.
move: (inordf_eqall _ to_nat i0) => H1.
rewrite H1 in it.
rewrite H1
Set Printing All.
apply ord_inj in H1.
have : inordf A to_nat i0 = to_nat i0.

apply (contraFneq false).
Set Printing All.
rewrite inordf_eqall in it.

apply gtn_eqF.

gtn_eqF: forall m n : nat, (m < n)%N -> (n == m) = false
ltn_eqF: forall m n : nat, (m < n)%N -> (m == n) = false



apply ord_inj in it.

Set Printing All.


Set Printing All.
symmetry.
rewrite -it.

move=> tep.

move/eqP.
move=> tr.


symmetry.
apply inordf_eq.
rewrite (inordf_eq.




rewrite /=.
rewrite (sum_parti _ _ (fun a => INR (to_nat a))).


rewrite -(pmf1 P) -dist_img -dist_nat_help.
rewrite /index_enum /@pr /Pr /=. 
Admitted.


End converse.




  ============================
   \rsum_(i<-index_iota 0 (\max_(a in A) to_nat a).+1)
      \rsum_(a | a \in [set x0 | X x0 == INR i]) `p_ X a =
   \rsum_(r<-undup [seq INR (to_nat a) | a <- enum A])
      \rsum_(i | (i \in A) && (INR (to_nat i) == r)) P i




 ============================
   \rsum_(i<-index_iota 0 (\max_(a <- Finite.enum A | a \in A) to_nat a).+1)
      \rsum_(a | a \in [set x0 | INR (to_nat x0) == INR i]) P a =
   \rsum_(r<-undup [seq INR (to_nat a) | a <- Finite.enum A])
      \big[Rplus/0]_(i <- Finite.enum A | INR (to_nat i) == r) P i



symmetry.

rewrite (partition_big (fun a => to_nat a) 
(fun i => i \in A)) /=.
rewrite /=.
rewrite (sum_parti _ _ (fun a => INR (to_nat a))).

Set Printing All.


rewrite /=.


(fun a => to_nat a)).




 -dist_img -dist_nat_help.
rewrite /@pr /Pr big_mkord.




Lemma reindex_onto (I J : finType) (h : J -> I) h' (P : pred I) F :
   (forall i, P i -> h (h' i) = i) ->
  \big[*%M/1]_(i | P i) F i =
    \big[*%M/1]_(j | P (h j) && (h' (h j) == j)) F (h j).


apply congr_big=> //.



rewrite /index_enum /=.
rewrite enumT.
elim (Finite.enum _).
  rewrite !big_nil big_nat_recr. big_nil /=.
  by rewrite /index_iota subn0 /= big_nil add0R.
move => a l IH.
rewrite big_mkord.
rewrite big_cons /=. 



apply Rplus_eq_compat_l.

have :  \rsum_(j<-undup [seq to_nat i | i <- l])
      \big[Rplus/0]_(a0 <- (a :: l) | a0
                                        \in [set x0 | 
                                      INR (to_nat x0) == 
                                      INR j]) P a0 =
  \rsum_(j<-undup [seq to_nat i | i <- l])
   (if a \in [set x0 | INR (to_nat x0) == INR j] then P a else 0) +
  \rsum_(j<-undup [seq to_nat i | i <- l])
      \big[Rplus/0]_(a0 <- l | a0 \in [set x0 | INR (to_nat x0) == INR j]) P a0.
rewrite -big_split /=.
apply eq_bigr => i _.
rewrite big_cons.
by case :(a \in [set x0 | INR (to_nat x0) == (INR i)])=> //; first  rewrite add0R.
move->.
have: \rsum_(j<-undup [seq INR (to_nat i) | i <- l])
      \big[Rplus/0]_(a0 <- (a :: l) | a0 \in [set x0 | INR (to_nat x0) == j])
         P a0 =
      \rsum_(j<-undup [seq INR (to_nat i) | i <- l])
        (if a \in [set x0 | INR (to_nat x0) == j] then P a else 0) +
      \rsum_(j<-undup [seq INR (to_nat i) | i <- l])
      \big[Rplus/0]_(a0 <- l | a0 \in [set x0 | INR (to_nat x0) == j])
         P a0.
rewrite -big_split /=.
apply eq_bigr => i _.
rewrite big_cons.
by case :(a \in [set x0 | INR (to_nat x0) == i])=> //; first  rewrite add0R.
move->.
rewrite IH.
rewrite addRC [in RHS] addRC.
apply Rplus_eq_compat_l.


elim l.
by rewrite !big_nil.
move=> a0 l0 IH'.
rewrite /=.

rewrite !big_cons. IH.



not_INR: forall n m : nat, n <> m -> INR n <> INR m

  rewrite /INR.

  simpl.




Admitted.

End converse.

Variables (n0 : nat) (T1 : eqType) (x1 : T1).
Variables (x : nat).
Implicit Type s : seq R.

Lemma map_f s x : x \notin s -> (INR x) \notin map INR s.
Proof.
elim: s => [|y s IHs] //=.
by case/predU1P=> [->|Hx]; [exact: predU1l | apply: predU1r; auto].
Qed.


  admit.
move->.
rewrite !big_cons.
by rewrite IH'.




rewrite eqbF_neg.
apply (map_f INR).
move: ninb'.
rewrite -negb_true_iff.



have : INR (to_nat a0) \in [seq INR (to_nat i) | i <- l0] = false.

  apply (map_f INR) in ninb'.
  rewrite -map_comp /funcomp in inb'.
  by rewrite inb'.
move->.
by rewrite IH'.

move: ninb'.
rewrite -negb_true_iff.
move=> aaa.


have : \rsum_(i<-if to_nat a \in [seq to_nat i | i <- l]
             then undup [seq to_nat i | i <- l]
             else to_nat a :: undup [seq to_nat i | i <- l])
      \big[Rplus/0]_(a1 <- (a :: l) | a1
                                        \in [set x0 | 
                                      INR (to_nat x0) == 
                                      INR i]) P a1 = 
\rsum_(i<-  undup [seq to_nat i | i <- l])
      \big[Rplus/0]_(a1 <- (a :: l) | a1
                                        \in [set x0 | 
                                      INR (to_nat x0) == 
                                      INR i]) P a1.
  apply congr_big => //.
  by rewrite inb.                         
move->.
have:  \rsum_(r<-if INR (to_nat a) \in [seq INR (to_nat i) | i <- l]
             then undup [seq INR (to_nat i) | i <- l]
             else INR (to_nat a) :: undup [seq INR (to_nat i) | i <- l])
      \big[Rplus/0]_(a0 <- (a :: l) | a0 \in [set x0 | INR (to_nat x0) == r])
         P a0 =
 \rsum_(r<- undup [seq INR (to_nat i) | i <- l])
      \big[Rplus/0]_(a0 <- (a :: l) | a0 \in [set x0 | INR (to_nat x0) == r])
         P a0.
  apply congr_big => //.
  apply (map_f INR) in inb.
  rewrite -map_comp /funcomp in inb.
  by rewrite inb.
move ->.
have :  \rsum_(i<-undup [seq to_nat i | i <- l])
      \big[Rplus/0]_(a1 <- (a :: l) | a1
                                        \in [set x0 | 
                                      INR (to_nat x0) == 
                                      INR i]) P a1 =
 \rsum_(i<-undup [seq to_nat i | i <- l])
   (if a \in [set x0 | INR (to_nat x0) == INR i]
              then P a else 0 ) + 
 \rsum_(i<-undup [seq to_nat i | i <- l])
 \big[Rplus/0]_(a1 <- l | a1 \in [set x0 |  INR (to_nat x0) == INR i]) P a1.
rewrite -big_split /=.
apply eq_bigr => i _.
rewrite big_cons.
by case :(a \in [set x0 | INR (to_nat x0) == INR i])=> //; first  rewrite add0R.
move->.
have: \rsum_(r<-undup [seq INR (to_nat i) | i <- l])
      \big[Rplus/0]_(a0 <- (a :: l) | a0 \in [set x0 | INR (to_nat x0) == r])
         P a0 =
    \rsum_(r<-undup [seq INR (to_nat i) | i <- l])
      (if a \in [set x0 | INR (to_nat x0) == r] then P a else 0) +
    \rsum_(r<-undup [seq INR (to_nat i) | i <- l])
      \big[Rplus/0]_(a0 <- l | a0 \in [set x0 | INR (to_nat x0) == r])
         P a0.
rewrite -big_split /=.
apply eq_bigr => i _.
rewrite big_cons.
by case :(a \in [set x0 | INR (to_nat x0) == i])=> //; first  rewrite add0R.
move->.
rewrite IH addRC [in RHS]addRC.
apply Rplus_eq_compat_l.
  elim l.
  by rewrite !big_nil.
  move => a0 l0 IH'.
  rewrite /=.
  have: {(to_nat a0 \in [seq to_nat i | i <- l0])= true} + {((to_nat a0 \in [seq to_nat i | i <- l0])) = false}.
   by move: Sumbool.sumbool_of_bool.
case=>[ inb' | ninb'].
have : \rsum_(i<-if to_nat a0 \in [seq to_nat i | i <- l0]
             then undup [seq to_nat i | i <- l0]
             else to_nat a0 :: undup [seq to_nat i | i <- l0])
      (if a \in [set x0 | INR (to_nat x0) == INR i] then P a else 0) =
       \rsum_(i<-undup [seq to_nat i | i <- l0])
      (if a \in [set x0 | INR (to_nat x0) == INR i] then P a else 0).
  apply congr_big => //.
  by rewrite inb'.                       
move ->.
have:   \rsum_(r<-if INR (to_nat a0) \in [seq INR (to_nat i) | i <- l0]
             then undup [seq INR (to_nat i) | i <- l0]
             else INR (to_nat a0) :: undup [seq INR (to_nat i) | i <- l0])
      (if a \in [set x0 | INR (to_nat x0) == r] then P a else 0) =
  \rsum_(r<-undup [seq INR (to_nat i) | i <- l0])
      (if a \in [set x0 | INR (to_nat x0) == r] then P a else 0).
  apply congr_big => //.
  apply (map_f INR) in inb'.
  rewrite -map_comp /funcomp in inb'.
  by rewrite inb'.
move->.
by rewrite IH'.





apply eq_bigr.



have :  \rsum_(i<-undup [seq to_nat i | i <- l])
      (if a \in [set x0 | INR (to_nat x0) == INR i] then P a else 0) +
   \rsum_(i<-undup [seq to_nat i | i <- l])
      \big[Rplus/0]_(a1 <- l | a1 \in [set x0 | INR (to_nat x0) == INR i])
         P a1 = 
   \rsum_(i<-undup [seq to_nat i | i <- l])
     ( (if a \in [set x0 | INR (to_nat x0) == INR i] then P a else 0) +
      \big[Rplus/0]_(a1 <- l | a1 \in [set x0 | INR (to_nat x0) == INR i])
         P a1).
  rewrite 

  apply big_ind3.
  rewrite big_mor

apply eq_bigr.
  

map_comp:
  forall (T1 T2 T3 : Type) (f1 : T2 -> T3) (f2 : T1 -> T2) (s : seq T1),
  [seq (f1 \o f2) i | i <- s] = [seq f1 i | i <- [seq f2 i | i <- s]]
m
move:inb.



map_f:
  forall (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1) (x : T1),
  x \in s -> f x \in [seq f i | i <- s]
mem_map:
  forall (T1 T2 : eqType) (f : T1 -> T2),
  injective f ->
  forall (s : seq T1) (x : T1), (f x \in [seq f i | i <- s]) = (x \in s)
index_map:
  forall (T1 T2 : eqType) (f : T1 -> T2),
  injective f ->
  forall (s : seq T1) (x : T1),
  seq.index (f x) [seq f i | i <- s] = seq.index x s
map_inj_uniq:
  forall (T1 T2 : eqType) (f : T1 -> T2),
  injective f -> forall s : seq T1, uniq [seq f i | i <- s] = uniq s
map_of_seq:
  forall (T1 : eqType) (T2 : Type) (s : seq T1) (fs : seq T2),
  T2 ->
  {f : T1 -> T2 | uniq s -> size fs = size s -> [seq f i | i <- s] = fs}


case to_nat a \in [seq to_nat i | i <- l].


  rewrite !big_nil big_nat_recr. big_nil /=.
  by rewrite /index_iota subn0 /= big_nil add0R.
move => a l IH.
rewrite big_mkord.
rewrite big_cons /=. 


Lemma dist_nat : \rsum_(0 <= i < (\max_(a| a \in A) to_nat a).+1) Pr[X = (INR i)] = 1.
Proof.
rewrite -(pmf1 P) -dist_img.
rewrite /img.
rewrite /@pr /Pr .
rewrite /index_enum /=.
rewrite enumT.
elim (Finite.enum _).
  rewrite !big_nil big_nat_recr. big_nil /=.
  by rewrite /index_iota subn0 /= big_nil add0R.
move => a l IH.
rewrite big_mkord.
rewrite big_cons /=. 



Set Printing All.
rewrite -enumT /=.


sum_parti:
  forall (A : finType) (p : seq A) (X F : A -> R),
  uniq p ->
  \rsum_(i<-p) F i =
  \rsum_(r<-undup [seq X i | i <- p]) \big[Rplus/0]_(i <- p | X i == r) F i
sum_parti_finType:
  forall (A : finType) (X F : A -> R),
  \rsum_(i | i \in A) F i =
  \rsum_(r<-undup [seq X i | i <- enum A])
     \rsum_(i | (i \in A) && (X i == r)) F i
big_undup:


apply big_ind2.


rewrite /index_enum /=.
Set Printing All.





rewrite -(pmf1 P).
rewrite /@pr /= /Pr.
elim (index_enum A).
  rewrite big_nat_recr /=.
  by rewrite !big_nil addR0.
move=> a l IH.
rewrite [in RHS]big_cons /=.
rewrite big_cons /=.
move: (le_lt_dec (\max_(j <- l | j \in A) to_nat j) (to_nat a)).
case.
move/leP.
rewrite leqNgt.
move=>H.
have : \rsum_(i<-index_iota 0
               (maxn (to_nat a) (\max_(j <- l | j \in A) to_nat j)).+1)
      \big[Rplus/0]_(a0 <- (a :: l) | a0
                                        \in [set x0 | 
                                      INR (to_nat x0) == 
                                      INR i]) P a0 =
\rsum_(i<-index_iota 0
                 (to_nat a).+1)
      \big[Rplus/0]_(a0 <- (a :: l) | a0
                                        \in [set x0 | 
                                      INR (to_nat x0) == 
                                      INR i]) P a0.
apply congr_big => //.
apply negbTE in H. 
by rewrite /maxn H.
move->.
apply negbTE in H. 

have :  \rsum_(i<(maxn (to_nat a) (\max_(j <- l | j \in A) to_nat j)).+1)
      \big[Rplus/0]_(a0 <- (a :: l) | a0
                                        \in [set x0 | 
                                      INR (to_nat x0) == 
                                      INR i]) P a0 = 
 \rsum_(i< (\max_(j <- l | j \in A) to_nat j).+1)
      \big[Rplus/0]_(a0 <- (a :: l) | a0
                                        \in [set x0 | 
                                      INR (to_nat x0) == 
                                      INR i]) P a0.

Set Printing All.
  apply congr_big.


case: (leq (to_nat a) (\max_(j <- l | j \in A) to_nat j))%N.
rewrite /maxn.
case
case (leq (to_nat a) (\max_(j <- l | j \in A) to_nat j)). maxn.


leqNgt: forall m n : nat, (m <= n)%N = ~~ (n < m)%N
ltnNge: forall m n : nat, (m < n)%N = ~~ (n <= m)%N





rewrite 
rewrite big_cons.
case : (a \in [set x0 | INR (to_nat x0) == INR 0]).
rewrite -addRA.
apply Rplus_eq_compat_l.
rewrite
rewrite big_nil.
rewrite {2}/maxn.
case :(lt_dec (to_nat a) (\max_(j <- l | j \in A) to_nat j)).
move/ltP.

Set Printing All.

(* =>lt_to_max. *)

(* rewrite /maxn /=. *)
(* rewrite to *)


(* =>[lt_to_max|lt_max_to]. *)


(* case: maxn. *)

(* rewrite IH. *)
(* case : (a \in [set x0 | INR (to_nat x0) == INR 0]). *)
(* rewrite -IH.  *)

(* Rewrite !big_nil. *)

(* rewrite /index_iota subn0 /= big_nil add0R. *)

(* move: (dist_support_not_empty P). *)
(* rewrite cardT -filter_index_enum. *)
(* elim (index_enum A). *)
(* done. *)
(* move=> a l IH card. *)

(* rewrite big_nil. *)
(* rewrite /@pr /= /Pr. *)
(* rewrite big_nat_recr /=. *)
(* rewrite /index_iota subn0 /= big_nil add0R. *)



rewrite -(pmf1 P).
remember (\max_(a in A) to_nat a) as max.
move: Heqmax.
elim max.
move=> H.
rewrite /@pr /= /Pr.
rewrite big_nat_recr /=.
rewrite /index_iota subn0 /= big_nil add0R.
have : leq (\max_(a in A) to_nat a) 0.
  by rewrite {2}H.
move/bigmax_leqP => H1. 
have : forall a : A, (to_nat a) = O.
move => a.
apply/eqP.
rewrite -leqn0.
by apply H1.
clear H1 => H1.
have left:  \rsum_(a | a \in [set x0 | INR (to_nat x0) == INR 0]) P a  <=
   \rsum_(a | a \in A) P a.
rewrite big_seq_cond.
apply Rle_big_P_true_f.
by apply pmf.
have right: \rsum_(a | a \in A) P a <=
 \rsum_(a | a \in [set x0 | INR (to_nat x0) == INR 0]) P a.
apply Rle_big_f_X_Y.
by apply pmf.
move => i H3.
rewrite inE.
by rewrite H1.
by apply Rle_antisym.

move => n0 H maxn.

Rle_big_f_X_Y:
  forall (A : finType) (f : A -> R) (P Q : pred A),
  (forall a : A, 0 <= f a) ->
  (forall i : A, i \in P -> i \in Q) ->
  \rsum_(i | i \in P) f i <= \rsum_(i | i \in Q) f i

rewrite big_seq_cond.
apply eq_bigl.
rewrite -inE.

Set Printing All.
rewrite H2.
have H2:  (fun x0 : A => (INR (to_nat x0)) == (INR O)) = (fun x0 : A => true).
Set Printing All.

have : forall a : A, (to_nat a) == O.
move => a.
by 

have : forall a : A, (leq 0 (to_nat a)) by move => a; apply leq0n.
apply 
apply/leP.
Set Printing All.
have : forall a : A, (to_nat a = 0)%N.
  move => a.
Set Printing All.
  apply bin_of_nat_inj.
  apply N.le_antisymm.
  simpl. Set Printing All.
  apply nat_of_bin_inj.
have: forall a , (to_nat a = 0)%N.
move=> a.

case/(N.lt_eq_cases (bin_of_nat (to_nat a))%N 0%N).
case; last first.
done. 
by move: (lt_n_0 (to_nat a)).
have :(to_nat a <= \max_(a in A) to_nat a)%coq_nat.
move: (leq_bigmax_cond ).

have : leq (\max_(a|a \in A) to_nat a) 0.


bigmax_leqP:
  forall (I : finType) (P : pred I) (m : nat) (F : I -> nat),
  ssrbool.reflect (forall i : I, P i -> (F i <= m)%N)
    (\max_(i | P i) F i <= m)%N
w
Set Printing All.
apply k.
move :leq_bigmax.
suff : False by done.

have : F i <= \rsum_(i|R i) F i.
  by apply Req_0_rmul_inv'.
rewrite -abs => ?.
fourier.

move: H.


rewrite /maxn /=.

  
rewrite -(pmf1 P).

rewrite /Ex /Pr.
transitivity (\rsum_(r <- img X) \rsum_(i in A | X i == r) (X i * `p_X i)).
  apply eq_bigr => r _.
  rewrite big_distrr /=.
  apply congr_big => //= a.
  by rewrite inE.
  by rewrite inE; move/eqP => ->.
by rewrite /img -sum_parti_finType.


apply eq_bigl.
rewrite /

move: H.

rewrite /maxn.

Set Printing All.
Set Printing All.
rewrite 
rewrite big_geq.


Lemma entropy_nat : `E --log P  = - \rsum_(i < (\max_(a| a \in A) to_nat a)) (Pr[X = (INR i)] * log (Pr[X = (INR i)])).


Set Printing All.



Lemma log_exp1_Rlt_0: 0 < log (exp 1).
Proof.
rewrite -log_1.
apply (log_increasing Rlt_zero_1).
apply (Rlt_trans _ 2 _ (Rlt_plus_1 _)).
apply exp_ineq1; by apply Rlt_zero_1.
Qed.


big_rem:
  forall (R : Type) (idx : R) (op : Monoid.com_law idx) 
    (I : eqType) (r : seq_predType I) (x : I) (P : pred I) 
    (F : I -> R),
  x \in r ->
  \big[op/idx]_(y <- r | P y) F y =
  op (if P x then F x else idx) (\big[op/idx]_(y <- rem x r | P y) F y)



Lemma helper: `H (`p_ X) <= log (exp 1) + log (`E X).
Proof.
have Ex_pos: 0 < `E X.
  have : forall a, 0 <= X a * `p_ X a=> elememt_nneg. 
    apply Rmult_le_pos; by [ apply (Rle_trans _ 1 _ (Rle_zero_1))| apply (Rle0f _)].    
  move Hpick : [pick a | Rlt_bool 0 (`p_ X a) ] => p.
  move: Hpick.
  case (pickP)=>[a | n_lt _].
    move/RltP=> ltzero _.
    have Xa_pos: 0 < X a by apply (Rlt_le_trans _ 1 _ (Rlt_zero_1)).
    apply (Rmult_lt_0_compat (X a) (`p_ X a) Xa_pos) in ltzero.
    by apply (pos_sumpos _ (mkPosFun  elememt_nneg) a).
  apply (big_pred0 0 Rplus (Finite.enum A) (fun a => `p_ X a)) in n_lt.
  have: \big[Rplus/0]_(i <- Finite.enum A | (fun a : A =>
                                             Rlt_bool 0 (`p_ X a)) i) `p_ X i=
        \rsum_(a | a \in A) `p_ X a.
    rewrite [in RHS]big_seq  /index_enum [in RHS](bigID (fun i => Rlt_bool 0 (`p_ X i))).
    rewrite  -!big_seq_cond -[X in X = _]addR0 /=.
    apply Rplus_eq_compat_l.
    apply Req_0_rmul=> i.
    rewrite -RleNgt.
    move/RleP=>[neg | zero];first by apply Rlt_not_le in neg; move: (Rle0f (`p_ X)).
    done.
  rewrite n_lt pmf1.
  by move: Rlt_zero_1; move  /Rlt_not_eq.
rewrite addRC -(log_mult (Ex_pos)); last first.
  apply exp_pos_pos; by apply Rlt_zero_1.
rewrite /Ex_alt (big_morph _ (morph_mulRDl _) (mul0R _)).
set g := fun i => X i * `p_ X i * exp 1.
rewrite (_ : \rsum_(i | i \in A) X i * `p_ X i * exp 1 = \rsum_(i | i \in A) g i); last first.
  by rewrite /g.
have g_pos : 0 <= \rsum_(i | i \in A) `p_ X i * log (g i).
  have : -(`H `p_ X) <= \rsum_(i | i \in A) `p_ X i * log (g i).
    rewrite Ropp_involutive.
    apply Rle_big_P_f_g=> i _.
    case (Rle0f (`p_ X) i) => [ pi_pos | <-]; last first.
      rewrite !mul0R; by  apply Rle_refl.
    apply (Rmult_le_compat_l _ _  _ (Rle0f (`p_ X) i)). 
    apply (log_increasing_le pi_pos).
    rewrite /g -mulRA mulRC -{1}(mulR1 (`p_ X i)) -mulRA.
    apply (Rmult_le_compat_l _ _ _ (Rle0f (`p_ X) i)). 

  apply Rle_big_0_P_g=> i _.
  case (Rle0f (`p_ X) i) => [ pi_pos | <-]; last first.
      rewrite mul0R; by  apply Rle_refl.
    apply (Rmult_le_pos _ _ (Rle0f (`p_ X) i)).
  rewrite log_mult; last first.
      by apply (Rlt_le_trans _ 2 _ Rlt_R0_R2 two_e).
    apply Rmult_lt_0_compat; by [apply (Rlt_le_trans _ 1 _ (Rlt_zero_1)) | apply pi_pos].
    

Set Printing All.


  rewrite -{1}(mulR0 (\rsum_(i | i \in A) `p_ X i)) (big_morph _ (morph_mulRDl _) (mul0R _)).
  apply Rle_big_P_f_g=> i _.
  rewrite /g mulR0 (mulRC (X i)).
  apply (Rmult_le_pos _ _ (Rle0f (`p_ X) i)).
  apply Rmult_le_pos.
  apply (Rmult_le_pos _ _ (Rle0f (`p_ X) i));  by apply Rlt_le.
  by apply Rlt_le; apply exp_pos_pos; by apply Rlt_zero_1.
apply (Rle_trans _ ( log (\rsum_(i | i \in A) g i) - \rsum_(i | i \in A) `p_ X i * log (g i))); last first.
  rewrite /Rminus -[X in _ <= X]addR0.
  apply Rplus_le_compat_l; apply Rge_le; apply Ropp_0_le_ge_contravar.
  
apply (Rplus_le_reg_l (\rsum_(i | i \in A) `p_ X i * g i)); rewrite Rplus_minus.
apply Ropp_le_cancel. 
rewrite Ropp_minus_distr.
rewrite [X in _ <= X](_ : X = \rsum(a | a \in A) `p_ X a * ( log (`p_ X a) - g i
have ()


rewrite -[X in _ <= X]big_split.

Ropp_minus_distr: forall r1 r2 : R, - (r1 - r2) = r2 - r1
Ropp_minus_distr': forall r1 r2 : R, - (r2 - r1) = r1 - r2



Rplus_minus: forall r1 r2 : R, r1 + (r2 - r1) = r2


Rlt_zero_1: 0 < 1

    rewrite -RleNgt in H.
    Set Printing All. simpl.
    apply eq_bigr.

    rewrite [in RHS](bigID _ (i \in A) (fun i => Rlt_bool 0 (`p_ X i)) ).
  have: \rsum_(a | a \in A) `p_ X a = \big[Rplus/0]_(i<- Finite.enum A | Rlt_bool 0 (`p_ X i)) `p_X 
    apply eq_bigl. 

big_rem:
  forall (R : Type) (idx : R) (op : Monoid.com_law idx) 
    (I : eqType) (r : seq_predType I) (x : I) (P : pred I) 
    (F : I -> R),
  x \in r ->
  \big[op/idx]_(y <- r | P y) F y =
  op (if P x then F x else idx) (\big[op/idx]_(y <- rem x r | P y) F y)

bigID:
  forall (R : Type) (idx : R) (op : Monoid.com_law idx) 
    (I : Type) (r : seq I) (a P : pred I) (F : I -> R),
  \big[op/idx]_(i <- r | P i) F i =
  op (\big[op/idx]_(i <- r | P i && a i) F i)
    (\big[op/idx]_(i <- r | P i && ~~ a i) F i)
bigU:
  forall (R : Type) (idx : R) (op : Monoid.com_law idx) 
    (I : finType) (A B : pred I) (F : I -> R),
  [disjoint A & B] ->
  \big[op/idx]_(i in [predU A & B]) F i =
  op (\big[op/idx]_(i in A) F i) (\big[op/idx]_(i in B) F i)


big_filter:
  forall (R : Type) (idx : R) (op : R -> R -> R) (I : Type) 
    (r : seq I) (P : pred I) (F : I -> R),
  \big[op/idx]_(i <- [seq x <- r | P x]) F i =
  \big[op/idx]_(i <- r | P i) F i
big_filter_cond:
  forall (R : Type) (idx : R) (op : R -> R -> R) (I : Type) 
    (r : seq I) (P1 P2 : pred I) (F : I -> R),
  \big[op/idx]_(i <- [seq x <- r | P1 x] | P2 i) F i =
  \big[op/idx]_(i <- r | P1 i && P2 i) F i

    

  apply (Rlt_big_0_g _ _ (dist_support_not_empty (rv_dist X)))=> i.
    case elememt_nneg with i; first done.
    apply (Req_0_rmul_inv _ _ elememt_nneg) with i in Ex_zero.
  


  apply (Rlt_big_0_g _ _ (dist_support_not_empty (rv_dist X)))=> i.
  rewrite -(mul0R (`p_ X i)).
  apply (Rmult_le_0_lt_compat _ _ _ _ (Rle_refl _)).

move: (dist_support_not_empty (rv_dist X)); move/card_gt0P.

predD1P:
  forall (T : eqType) (x y : T) (b : bool),
  ssrbool.reflect (x <> y /\ b) ((x != y) && b)

"x != y" := negb (eq_op x y)

rsum_neq0:
  forall (A : finType) (P : {set A}) (g : A -> R),
  \rsum_(t | t \in P) g t != 0 -> [exists t, (t \in P) && (g t != 0)]


  forall (T : finType) (A : pred T),
  ssrbool.reflect (exists i : T, i \in A) (0 < #|A|)%N


Search (0 < #| _ |)%N.

move: (Rlt_le_neq (Ex_alt_pos X_pos) E_nonzero)=> E_pos.






case (Rlt_or_le (`H P) (log (`E X)))=> [ lt_HE | lt_EH].
  by rewrite -(add0R (`H P)); apply Rlt_le; apply (Rplus_le_lt_compat _ _ _ _ log_exp1_Rle_0).


set X := mkRvar P f. 
have Ex_pos: 0 <= `E X by apply Ex_alt_pos; apply Rle0f.
case: Ex_pos=> [Ex_pos | zero]; last first.
  by symmetry in zero.
case (Rlt_or_le (`H P) (log (`E X)))=> [ lt_HE | lt_EH].
  by rewrite -(add0R (`H P)); apply Rlt_le; apply (Rplus_le_lt_compat _ _ _ _ log_exp1_Rle_0).
set x := `H P - log (`E X).
rewrite (_ : `H P = x * ( log (2 * x) - log x) + log (`E X)); last first.
  rewrite (log_mult Rlt_R0_R2); last first.
    rewrite /x.
    apply (Rplus_lt_reg_r ( log (`E X))).
    by rewrite addR0 addRC /Rminus -addRA Rplus_opp_l addR0.
  rewrite log_2 (_ : 1 + log x - log x = 1); last first.
    apply (Rplus_eq_reg_l (- 1)).
    by rewrite addRA addRA Rplus_opp_l add0R Rplus_opp_r.
  by rewrite mulR1 addRC /x Rplus_minus.
apply Rplus_lt_compat_r.
rewrite -(mul1R (log (exp _))).
apply (Rlt_trans _ (x * log (exp 1))).
rewrite {4}(_ : x = 2 * x - x).
apply div_diff_ub.



rewrite -(log_exp2 (`H P)) in lt_EH.
apply Rgt_lt in lt_EH;  apply (log_lt_inv Ex_pos (exp2_pos _ )) in lt_EH.
set x := `E X / ((exp2 (`H P)) - `E X ).
have x_neg : 0 < x.
  apply (Rmult_lt_reg_r ((exp2 (`H P)) - `E X)).
    apply (Rplus_lt_reg_r (`E X)).
    by rewrite addR0 addRC /Rminus -addRA Rplus_opp_l addR0.
  rewrite mul0R /x /Rdiv -mulRA -Rinv_l_sym. 
    by rewrite mulR1.
  apply Rgt_not_eq; apply Rlt_gt.
  apply (Rplus_lt_reg_r (`E X)).
  by rewrite addR0 addRC /Rminus -addRA Rplus_opp_l addR0.
have : `H P = log (x + 1) - log x + log (`E X).
  rewrite -addRA -(log_Rinv x_neg) addRA (addRC _ 1) -(log_mult (Rlt_zero_pos_plus1 _ x_neg) (Rinv_0_lt_compat _ x_neg)).
  rewrite Rmult_plus_distr_r mul1R -(Rinv_r_sym _); last first.
    apply Rgt_not_eq; by apply Rlt_gt.
    rewrite -(log_mult _ Ex_pos); last first.
    apply Rle_lt_0_plus_1; apply Rlt_le.
    apply (Rmult_lt_reg_r x _ _ x_neg).
    rewrite mul0R -(Rinv_l_sym _); last first.
      apply Rgt_not_eq; by apply Rlt_gt.
    by apply Rlt_0_1.
  rewrite (_ : / x = (exp2 (`H P) - `E X) / `E X); last first.
    rewrite (Rinv_mult_distr _ _ E_nonzero); last first.
        apply Rinv_neq_0_compat; apply Rgt_not_eq; apply Rlt_gt.
        apply (Rplus_lt_reg_r (`E X)).
        by rewrite addR0 addRC /Rminus -addRA Rplus_opp_l addR0.
    apply (Rmult_eq_reg_l (`E X)); last first.
      done.
    rewrite /x /Rdiv [in RHS]mulRC -mulRA [in LHS]mulRA.
    rewrite -(Rinv_r_sym _ E_nonzero) mul1R -(Rinv_l_sym _ E_nonzero) mulR1 Rinv_involutive.
    done.
    apply Rgt_not_eq; apply Rlt_gt; apply (Rplus_lt_reg_r (`E X)).
    by rewrite addR0 addRC /Rminus -addRA Rplus_opp_l addR0.
  rewrite Rmult_plus_distr_r mul1R /Rdiv -mulRA -(Rinv_l_sym _ E_nonzero) mulR1.
  by rewrite  -addRA Rplus_opp_l addR0 log_exp2.
move ->.
apply Rplus_lt_compat_r
apply div_diff_ub.

have x1_neg : 0 < x + 1.
  Rlt_zero_pos_plus1

  rewrite log_mult

Rle_big_eq_0:
  forall (B : finType) (g : B -> R) (U : pred B),
  \rsum_(i | U i) g i = 0 ->
  (forall i : B, U i -> 0 <= g i) -> forall i : B, U i -> g i = 0

Req_0_rmul_inv:
  forall (C : finType) (R1 : pred C) (F : C -> R),
  (forall a : C, 0 <= F a) ->
  0 = \rsum_(i | R1 i) F i -> forall i : C, R1 i -> 0 = F i


Lemma log_sum_inequality: 

Lemma test : ln 0 = 0.
Proof.
rewrite /ln.
case Rlt_dec=>r. 
fourier.
done.
Qed.

Lemma test1: log 0 = 0.
Proof.
rewrite /log test.
apply  (Rmult_eq_reg_r (ln 2)).
rewrite /Rdiv -mulRA -Rinv_l_sym.
by do 2rewrite mul0R.
apply Rlt_dichotomy_converse.
right.
apply (Rplus_gt_reg_neg_r _ 2 _).
apply (Rplus_gt_reg_l 2).
symmetry. apply Rlt_not_eq.



Section test.
Local Open Scope nat_scope.

Lemma test1 : forall A B, A /\ B <-> B /\ A.
Proof. 
move => A B.
by apply conj; case.
Qed.

Lemma test2 : forall A B, A -> (A -> B) -> B.
Proof.
move => A B Atrue.
by apply.
Qed.

Lemma test3 : forall n : nat,  2 * n = n + n.
Proof. 
elim. 
  by rewrite muln0.
move => n IH.
by rewrite mulnS IH (addSn n n.+1) addnS add2n.
Qed.

Lemma test4 : forall n, beq_nat n 0 = true -> n = 0.
Proof.
by case.
Qed.

Lemma test5 : forall x : nat, (x = 2) -> (2*x = 4).
Proof. 
 by move=> k hyp; rewrite hyp; clear hyp.
Qed.

Lemma test6 n m: m <= n -> n - (n - m) = m. 
Proof. 
elim: n m => [|m IHm] [|n] //. 
move=> H.
by rewrite subn0 subnn.
move => H.
rewrite -{2}(IHm n).
rewrite -addn1.
Lemma subnKC m n : m <= n -> m + (n - m) = n.
Proof. elim: m n => [|m IHm] [|n] .  by [].
by [].
by [].
move => IHn.
apply IHm in IHn.
by rewrite -{2}IHn.


Definition subn_rec := minus.
Notation "m - n" := (subn_rec m n) : nat_rec_scope.

Definition subn := nosimpl subn_rec.
Notation "m - n" := (subn m n) : nat_scope.

rewrite subnBA; last first.
by [].

rewrite -addnA.
rewrite /addn.
 

Set Printing All.


Lemma KEISAN : forall a b : nat, a = 3 -> b = 2 -> a + b = 5.
Proof.
by move=> _ _ -> ->.
move => a b a3 b2.
rewrite a3 {a3} b2.


rewrite a3  {}b2.
rewrite a3 {a3} b2.
rewrite a3 {} b2 {b2}.
rewrite a3 {} b2 {}.


f : convex <=> f (t x + (1 - t) y) <= t f (x) + (1 - t) f (y)
           <=> 

R1 / (R1 + R2 + R3) > 0 -> 

R1 >0 -> f (R2 / R1) R1 <= R3

(x1 >0 -> f (x2 / x1) x1 <= x3)
(y1 >0 -> f (y2 / y1) y1 <= y3)

x1 + y2 >0 -> f (

!eqxx



条件を強める /\を付ける




K : fun R1 R2 R3 => 
      R1 > 0 -> f (R2 /(R1 + R2)) <= R3 / (R1 + R3)
      R1 > R2 -> f (R2 /         




pg-ssr.el


Lemma rsum_if B b (s1 s2 : seq B) (Q : B -> R):
\rsum_(r<-if b then s1 else s2) Q r = 
    if b then \rsum_(r<-s1) Q r else \rsum_(r<-s2) Q r.
Proof.
by case:b=> //.
Qed.

Lemma rsum_rsum_cons B (lb: seq B) l a Q:
\rsum_(i<- lb) \big[Rplus/0]_(a1 <- (a :: l) | a1 \in [set x | Q x i]) P a1 =
  \rsum_(i<- lb)(if (a \in [set x | Q x i]) then P a else 0) + 
  \rsum_(i<- lb) \big[Rplus/0]_(a1 <- l | a1 \in [set x | Q x i]) P a1.
Proof.
rewrite -big_split /=.
apply eq_bigr => i _.
rewrite big_cons.
by case :(a \in [set x |Q x i])=> //; first  rewrite add0R.
Qed.

Lemma dist_img : \rsum_(r <- img X) Pr[X = r] = \rsum_(a|a \in A) P a.
Proof.
rewrite /Ex /Pr.
transitivity (\rsum_(r <- img X) \rsum_(i in A | X i == r) `p_X i).
  apply eq_bigr => r _.
  apply congr_big => //= a.
  by rewrite inE.
by rewrite /img -sum_parti_finType.
Qed.

Lemma dist_nat_help :  \rsum_(i<- undup [seq to_nat i | i <- enum A])
      \rsum_(a | a \in [set x0 | X x0 == INR i]) `p_ X a =
   \rsum_(r<-undup [seq X i | i <- enum A])
      \rsum_(a | a \in [set x0 | X x0 == r]) `p_ X a.
Proof.
rewrite /X /=.
rewrite /index_enum /=.
rewrite enumT.
elim (Finite.enum _).
  by rewrite !big_nil.
move=> a l IH.
rewrite /=.
case:(Sumbool.sumbool_of_bool (to_nat a \in [seq to_nat i | i <- l]))=>[inb | ninb].
  rewrite !rsum_if !rsum_rsum_cons inb.
  move: inb.
  rewrite -(mem_map INR_eq) -map_comp; move->.
  rewrite IH addRC [in RHS]addRC.
  apply Rplus_eq_compat_l.
  elim l=>[| a0 l0 IH' /=]; first by rewrite !big_nil.
  case:(Sumbool.sumbool_of_bool (to_nat a0 \in [seq to_nat i | i <- l0]))=>[inb | ninb].
  rewrite !rsum_if inb.
  move: inb.
  by rewrite -(mem_map INR_eq) -map_comp; move->.
  rewrite !rsum_if ninb.
  move: ninb.
  move/INR_map ->.
  by rewrite !big_cons IH'.
rewrite !rsum_if !rsum_rsum_cons ninb !big_cons.
move: ninb.
move/INR_map ->.
rewrite IH addRC [in RHS]addRC addRA [in RHS]addRA.
apply Rplus_eq_compat_l.
  elim l=>[| a0 l0 IH' /=]; first by rewrite !big_nil.
  case:(Sumbool.sumbool_of_bool (to_nat a0 \in [seq to_nat i | i <- l0]))=>[inb | ninb].
  rewrite !rsum_if inb.
  move: inb.
  by move/INR_map ->.
  rewrite !rsum_if ninb.
  move: ninb.
  move/INR_map ->.
  by rewrite !big_cons IH'.
Qed.
