import PhysLean.StatisticalMechanics.SpinGlasses.HopfieldNetwork.BoltzmannMachine
import Mathlib
import PhysLean.StatisticalMechanics.CanonicalEnsemble.Finite
import PhysLean.StatisticalMechanics.CanonicalEnsemble.Lemmas

-- Provide a finite canonical ensemble instance for the Hopfield Boltzmann construction.
instance
  {U σ : Type} [Fintype U] [DecidableEq U]
  (NN : NeuralNetwork ℝ U σ) [Fintype NN.State] [Nonempty NN.State]
  [TwoStateNeuralNetwork NN] [TwoState.TwoStateExclusive NN]
  (spec : TwoState.EnergySpec' (NN:=NN)) (p : Params NN) :
  CanonicalEnsemble.IsFinite (HopfieldBoltzmann.CEparams (NN:=NN) (spec:=spec) p) := by
  classical
  have _ : IsHamiltonian (U:=U) (σ:=σ) NN := IsHamiltonian_of_EnergySpec' spec
  dsimp [HopfieldBoltzmann.CEparams]
  infer_instance

variable [Fintype ι] [DecidableEq ι] [Ring R] --[CommRing R]
open CanonicalEnsemble Constants

section DetailedBalance
open scoped Classical
open TwoState HopfieldBoltzmann

variable {U σ : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (NN : NeuralNetwork ℝ U σ) [Fintype NN.State] [Nonempty NN.State]
variable [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
variable (spec : TwoState.EnergySpec' (NN:=NN))
variable (p : Params NN) (T : Temperature)

local notation "P" => P (NN:=NN) (spec:=spec) p T
local notation "K" => Kbm (NN:=NN) p T

/-- Helper: states differ away from `u` (∃ other coordinate with different activation). -/
def DiffAway (u : U) (s s' : NN.State) : Prop :=
  ∃ v, v ≠ u ∧ s.act v ≠ s'.act v

omit [Fintype U] [Nonempty U] [Fintype NN.State] [Nonempty NN.State] [TwoStateExclusive NN] in
/-- If the states differ away from the update site, both transition probabilities vanish. -/
lemma Kbm_zero_of_diffAway
    {u : U} {s s' : NN.State}
    (h : DiffAway (NN:=NN) u s s') :
    K (u:=u) s s' = 0 ∧ K (u:=u) s' s = 0 := by
  classical
  rcases h with ⟨v, hv_ne, hv_diff⟩
  have h_ne_pos  : s' ≠ updPos (NN:=NN) s u := by
    intro h_eq
    have hc   := congrArg (fun st : NN.State => st.act v) h_eq
    have hupd : (updPos (NN:=NN) s u).act v = s.act v := by
      simp [updPos_act_noteq (NN:=NN) s u v hv_ne]
    have : s'.act v = s.act v := by simpa [hupd] using hc
    exact hv_diff (id (Eq.symm this))
  have h_ne_neg  : s' ≠ updNeg (NN:=NN) s u := by
    intro h_eq
    have hc   := congrArg (fun st : NN.State => st.act v) h_eq
    have hupd : (updNeg (NN:=NN) s u).act v = s.act v := by
      simp [updNeg_act_noteq (NN:=NN) s u v hv_ne]
    have : s'.act v = s.act v := by simpa [hupd] using hc
    exact hv_diff (id (Eq.symm this))
  have h_forward : Kbm (NN:=NN) p T u s s' = 0 :=
    Kbm_apply_other (NN:=NN) (p:=p) (T:=T) u s  s' h_ne_pos h_ne_neg
  have h_ne_pos' : s ≠ updPos (NN:=NN) s' u := by
    intro h_eq
    have hc   := congrArg (fun st : NN.State => st.act v) h_eq
    have hupd : (updPos (NN:=NN) s' u).act v = s'.act v := by
      simp [updPos_act_noteq (NN:=NN) s' u v hv_ne]
    have : s.act v = s'.act v := by simpa [hupd] using hc
    exact hv_diff this
  have h_ne_neg' : s ≠ updNeg (NN:=NN) s' u := by
    intro h_eq
    have hc   := congrArg (fun st : NN.State => st.act v) h_eq
    have hupd : (updNeg (NN:=NN) s' u).act v = s'.act v := by
      simp [updNeg_act_noteq (NN:=NN) s' u v hv_ne]
    have : s.act v = s'.act v := by simpa [hupd] using hc
    exact hv_diff this
  have h_backward : Kbm (NN:=NN) p T u s' s = 0 :=
    Kbm_apply_other (NN:=NN) (p:=p) (T:=T) u s' s h_ne_pos' h_ne_neg'
  exact ⟨h_forward, h_backward⟩

omit [Nonempty U] [Nonempty NN.State] in
/-- Detailed balance holds trivially in the “diff-away” case (both transition probabilities are 0). -/
lemma detailed_balance_diffAway
  {u : U} {s s' : NN.State}
  (h : DiffAway (NN:=NN) u s s') :
  P s * K (u:=u) s s' = P s' * K (u:=u) s' s := by
  classical
  rcases Kbm_zero_of_diffAway (NN:=NN) (p:=p) (T:=T) h with ⟨h1, h2⟩
  simp [h1, h2]

omit [Fintype U] [Nonempty U] [Fintype NN.State] [Nonempty NN.State] in
/-- Classification of the single-site difference at `u` (exclusive two-state case). -/
lemma single_site_cases
    {u : U} {s s' : NN.State}
    (h_off : ∀ v ≠ u, s.act v = s'.act v)
    (h_ne : s ≠ s') :
    (s.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN) ∧
       s'.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN))
  ∨ (s.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN) ∧
       s'.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN)) := by
  classical
  have hx : s.act u ≠ s'.act u := by
    intro hcontra
    apply h_ne
    ext v
    by_cases hv : v = u
    · simp [hv, hcontra]
    · simpa [hv] using h_off v hv
  rcases (TwoStateExclusive.pact_iff (NN:=NN) (a:=s.act u)).1 (s.hp u) with hs_pos | hs_neg
  · rcases (TwoStateExclusive.pact_iff (NN:=NN) (a:=s'.act u)).1 (s'.hp u) with hs'_pos | hs'_neg
    · exact False.elim (hx (hs_pos.trans hs'_pos.symm))
    · exact Or.inl ⟨hs_pos, hs'_neg⟩
  · rcases (TwoStateExclusive.pact_iff (NN:=NN) (a:=s'.act u)).1 (s'.hp u) with hs'_pos | hs'_neg
    · exact Or.inr ⟨hs_neg, hs'_pos⟩
    · exact False.elim (hx (hs_neg.trans hs'_neg.symm))

/-- Convenience: `logisticProb (-x) = 1 - logisticProb x` (already available above as
`TwoState.logisticProb_neg`, re-exposed here in the local namespace for algebra lemmas). -/
lemma logistic_neg (x : ℝ) :
    logisticProb (-x) = 1 - logisticProb x :=
  TwoState.logisticProb_neg x

/-- Algebraic lemma: `(1 - logisticProb x) = logisticProb (-x)`. -/
lemma one_sub_logistic_eq_logistic_neg (x : ℝ) :
    1 - logisticProb x = logisticProb (-x) := by
  simp [logistic_neg x]

/-- Denominator non‑zero: `1 - logisticProb x ≠ 0`. -/
lemma one_sub_logistic_ne_zero (x : ℝ) :
    1 - logisticProb x ≠ 0 := by
  have hxlt : logisticProb x < 1 := TwoState.logisticProb_lt_one x
  exact sub_ne_zero_of_ne (ne_of_lt hxlt).symm

/-- Positivity: `logisticProb x > 0`. -/
lemma logisticProb_pos' (x : ℝ) : 0 < logisticProb x :=
  TwoState.logisticProb_pos x

/-- Nonnegativity of the complement: `0 < 1 - logisticProb x`. -/
lemma one_sub_logistic_pos (x : ℝ) : 0 < 1 - logisticProb x := by
  have hxlt : logisticProb x < 1 := TwoState.logisticProb_lt_one x
  linarith

lemma logistic_div_one_sub_logistic (x : ℝ) :
    logisticProb x / (1 - logisticProb x) = Real.exp x := by
  have hbase : (1 - logisticProb x) / logisticProb x = Real.exp (-x) :=
    one_sub_logistic_div_logistic x
  have hpos  : logisticProb x ≠ 0 := (ne_of_gt (logisticProb_pos' x))
  have hden  : 1 - logisticProb x ≠ 0 := one_sub_logistic_ne_zero x
  have hrecip :
      logisticProb x / (1 - logisticProb x)
        = ((1 - logisticProb x) / logisticProb x)⁻¹ := by
    field_simp [hpos, hden]
  calc
    logisticProb x / (1 - logisticProb x)
        = ((1 - logisticProb x) / logisticProb x)⁻¹ := hrecip
    _ = (Real.exp (-x))⁻¹ := by simp [hbase]
    _ = Real.exp x := by simp [Real.exp_neg]

/-- Ratio identity: `logisticProb x / logisticProb (-x) = exp x`. -/
lemma logistic_ratio_neg (x : ℝ) :
    logisticProb x / logisticProb (-x) = Real.exp x := by
  have hden_ne : logisticProb (-x) ≠ 0 := (ne_of_gt (logisticProb_pos' (-x)))
  have hden : logisticProb (-x) = 1 - logisticProb x := logistic_neg x
  calc
    logisticProb x / logisticProb (-x)
        = logisticProb x / (1 - logisticProb x) := by simp [hden]
    _ = Real.exp x := logistic_div_one_sub_logistic x

/-- Ratio identity in inverted orientation: `logisticProb (-x) / logisticProb x = exp (-x)`. -/
lemma logistic_ratio (x : ℝ) :
    logisticProb (-x) / logisticProb x = Real.exp (-x) := by
  simpa [neg_neg] using logistic_ratio_neg (-x)

/-- Paired flip probabilities (general `EnergySpec'`).  For a site `u`, set
`sPos  := updPos s u`, `sNeg := updNeg s u` and
`Δ     := f (spec.E p sPos - spec.E p sNeg)`.
Then
```
probPos f p T s     u = logisticProb (-Δ * β)
probPos f p T sNeg  u = logisticProb (-Δ * β)
``` -/
lemma TwoState.EnergySpec'.probPos_flip_pair
    {U σ} [Fintype U] [DecidableEq U]
    {NN : NeuralNetwork ℝ U σ} [TwoStateNeuralNetwork NN]
    (spec : TwoState.EnergySpec' (NN:=NN))
    (p : Params NN) (T : Temperature) (s : NN.State) (u : U) :
    let f    := (RingHom.id ℝ)
    let sPos := updPos (NN:=NN) s u
    let sNeg := updNeg (NN:=NN) s u
    let Δ    := f (spec.E p sPos - spec.E p sNeg)
    probPos (NN:=NN) f p T s    u = logisticProb (-Δ * (T.β : ℝ)) ∧
    probPos (NN:=NN) f p T sNeg u = logisticProb (-Δ * (T.β : ℝ)) := by
  classical
  intro f sPos sNeg Δ
  let ES : TwoState.EnergySpec (NN:=NN) :=
    { E                 := spec.E
      , localField       := spec.localField
      , localField_spec  := spec.localField_spec
      , flip_energy_relation := by
          intro f' p' s' u'
          simpa using spec.flip_energy_relation f' p' s' u' }
  have hPos : updPos (NN:=NN) s u = sPos := rfl
  have hNeg : updNeg (NN:=NN) s u = sNeg := rfl
  have h₁ : probPos (NN:=NN) f p T s u =
      logisticProb (-Δ * (T.β : ℝ)) := by
    have h := ES.probPos_eq_of_energy f p T s u
    dsimp [ES] at h
    simpa [hPos, hNeg, Δ, sub_eq_add_neg,
           mul_comm, mul_left_comm, mul_assoc] using h
  have hPos' : updPos (NN:=NN) sNeg u = sPos := by
    ext v
    by_cases hv : v = u
    · subst hv; simp [sPos, sNeg, updPos, updNeg]
    · simp [sPos, sNeg, updPos, updNeg, hv]
  have hNeg' : updNeg (NN:=NN) sNeg u = sNeg := by
    ext v
    by_cases hv : v = u
    · subst hv; simp [sNeg, updNeg]
    · simp [sNeg, updNeg, hv]
  have h₂ : probPos (NN:=NN) f p T sNeg u =
      logisticProb (-Δ * (T.β : ℝ)) := by
    have h := ES.probPos_eq_of_energy f p T sNeg u
    dsimp [ES] at h
    simpa [hPos', hNeg', Δ, sub_eq_add_neg,
           mul_comm, mul_left_comm, mul_assoc] using h
  exact ⟨h₁, h₂⟩

/-- Specialization of the previous pair lemma to the “neg→pos” orientation used
in `detailed_balance_neg_pos`.  Here `ΔE = E s' - E s` with `s' = updPos s u`
and `s = updNeg s' u` (i.e. `s` carries σ_neg at `u`, `s'` carries σ_pos). -/
lemma flip_prob_neg_pos
    {U σ} [Fintype U] [DecidableEq U]
    {NN : NeuralNetwork ℝ U σ} [TwoStateNeuralNetwork NN]
    (spec : TwoState.EnergySpec' (NN:=NN))
    (p : Params NN) (T : Temperature)
    {s s' : NN.State} {u : U}
    (h_off : ∀ v ≠ u, s.act v = s'.act v)
    (h_neg : s.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN))
    (h_pos : s'.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN)) :
    let ΔE := spec.E p s' - spec.E p s
    probPos (NN:=NN) (RingHom.id ℝ) p T s u = logisticProb (-(T.β : ℝ) * ΔE) ∧
    probPos (NN:=NN) (RingHom.id ℝ) p T s' u = logisticProb (-(T.β : ℝ) * ΔE) := by
  classical
  intro ΔE
  have h_sPos : updPos (NN:=NN) s u = s' := by
    ext v; by_cases hv : v = u
    · subst hv; simp [updPos_act_at_u, h_pos]
    · simp [updPos_act_noteq (NN:=NN) s u v hv, h_off v hv]
  have h_sNeg : updNeg (NN:=NN) s u = s := by
    ext v; by_cases hv : v = u
    · subst hv; simp [updNeg_act_at_u, h_neg]
    · simp [updNeg_act_noteq (NN:=NN) s u v hv]
  obtain ⟨h_prob_s, _⟩ :=
    (TwoState.EnergySpec'.probPos_flip_pair (NN:=NN) spec p T s u)
  have hΔ₁ :
      (RingHom.id ℝ)
          (spec.E p (updPos (NN:=NN) s u) - spec.E p (updNeg (NN:=NN) s u))
        = ΔE := by
    simp [ΔE, h_sPos, h_sNeg]
  have h1 :
      probPos (NN:=NN) (RingHom.id ℝ) p T s u
        = logisticProb (-(T.β : ℝ) * ΔE) := by
    rw [h_prob_s, hΔ₁]
    ring_nf
  have h_s'Pos : updPos (NN:=NN) s' u = s' := by
    ext v; by_cases hv : v = u
    · subst hv; simp [updPos_act_at_u, h_pos]
    · simp [updPos_act_noteq (NN:=NN) s' u v hv]
  have h_s'Neg : updNeg (NN:=NN) s' u = s := by
    ext v; by_cases hv : v = u
    · subst hv; simp [updNeg_act_at_u, h_neg]
    · simp [updNeg_act_noteq (NN:=NN) s' u v hv, (h_off v hv).symm]
  obtain ⟨_, h_prob_s'⟩ :=
    (TwoState.EnergySpec'.probPos_flip_pair (NN:=NN) spec p T s' u)
  have hΔ₂ :
      (RingHom.id ℝ)
          (spec.E p (updPos (NN:=NN) s' u) - spec.E p (updNeg (NN:=NN) s' u))
        = ΔE := by
    simp [ΔE, h_s'Pos, h_s'Neg, neg_sub]
  have h2 :
      probPos (NN:=NN) (RingHom.id ℝ) p T s' u
        = logisticProb (-(T.β : ℝ) * ΔE) := by
    simp [h_prob_s', hΔ₂]
    ring_nf; aesop
  exact ⟨h1, h2⟩

/-- Clean algebraic lemma:
    if
    • `Pfun s' / Pfun s  = exp (-β ΔE)` and
    • `Kfun s  s' / Kfun s' s = exp ( β ΔE)`
    then detailed balance holds: `Pfun s * Kfun s s' = Pfun s' * Kfun s' s`. -/
lemma detailed_balance_from_opposite_ratios
    {α : Type}
    {Pfun : α → ℝ}            -- one-argument  (probability)  function
    {Kfun : α → α → ℝ}        -- two-argument (kernel)       function
    {s s' : α} {β ΔE : ℝ}
    (hP  :  Pfun s' / Pfun s        = Real.exp (-β * ΔE))
    (hK  :  Kfun s  s' / Kfun s' s  = Real.exp (-β * ΔE))
    (hPpos : 0 < Pfun s) (hKpos : 0 < Kfun s' s) :
    Pfun s * Kfun s s' = Pfun s' * Kfun s' s := by
  have hPne : Pfun s ≠ 0 := (ne_of_gt hPpos)
  have hKne : Kfun s' s ≠ 0 := (ne_of_gt hKpos)
  have hEqRat : Pfun s' / Pfun s = Kfun s s' / Kfun s' s := by
    simp [hP, hK]
  have hP' : Pfun s' = (Kfun s s' / Kfun s' s) * Pfun s := by
    have := hEqRat
    exact (div_eq_iff hPne).1 this
  have hFinal :
      Pfun s' * Kfun s' s = Kfun s s' * Pfun s := by
    have hK' : Kfun s' s ≠ 0 := hKne
    calc
      Pfun s' * Kfun s' s
          = (Kfun s s' / Kfun s' s * Pfun s) * Kfun s' s := by simp [hP']
      _ = (Kfun s s' * (Kfun s' s)⁻¹ * Pfun s) * Kfun s' s := by
            simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ = Kfun s s' * Pfun s * ((Kfun s' s)⁻¹ * Kfun s' s) := by
            ring_nf
      _ = Kfun s s' * Pfun s := by
            simp [hK']
  simpa [mul_comm, mul_left_comm, mul_assoc] using hFinal.symm

omit [Nonempty U] in
lemma detailed_balance_neg_pos
    {u : U} {s s' : NN.State}
    (h_off : ∀ v ≠ u, s.act v = s'.act v)
    (h_neg : s.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN))
    (h_pos : s'.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN)) :
    P s * K (u:=u) s s' = P s' * K (u:=u) s' s := by
  classical
  have h_updPos : s' = updPos (NN:=NN) s u := by
    ext v; by_cases hv : v = u
    · subst hv; simp [updPos_act_at_u, h_pos]
    · simp [updPos_act_noteq (NN:=NN) s u v hv, h_off v hv]
  have h_updNeg : s = updNeg (NN:=NN) s' u := by
    ext v; by_cases hv : v = u
    · subst hv; simp [updNeg_act_at_u, h_neg]
    · have := h_off v hv; simp [updNeg_act_noteq (NN:=NN) s' u v hv, this.symm]
  have hK_fwd :
      K (u:=u) s s' = probPos (RingHom.id ℝ) p T s u := by
    subst h_updPos
    simpa [Kbm] using
      (Kbm_apply_updPos (NN:=NN) (p:=p) (T:=T) u s)
  have hK_bwd :
      K (u:=u) s' s = 1 - probPos (RingHom.id ℝ) p T s' u := by
    subst h_updNeg
    simpa [Kbm] using
      (Kbm_apply_updNeg (NN:=NN) (p:=p) (T:=T) u s')
  let ΔE := spec.E p s' - spec.E p s
  obtain ⟨hProb_fwd, hProb_bwd⟩ :=
    flip_prob_neg_pos (NN:=NN) (spec:=spec) p T
      (s:=s) (s':=s') (u:=u) h_off h_neg h_pos
  have hKf :
      K (u:=u) s s' = logisticProb (-(T.β : ℝ) * ΔE) := by
    simp [hK_fwd, hProb_fwd, ΔE, mul_comm, mul_left_comm, mul_assoc]
  have hKb :
      K (u:=u) s' s = logisticProb ((T.β : ℝ) * ΔE) := by
    have hbwdprob :
        probPos (RingHom.id ℝ) p T s' u
          = logisticProb (-(T.β : ℝ) * ΔE) := by
      simpa [ΔE, mul_comm, mul_left_comm, mul_assoc] using hProb_bwd
    have hneg := logistic_neg ((T.β : ℝ) * ΔE)
    have : 1 - probPos (RingHom.id ℝ) p T s' u
            = logisticProb ((T.β : ℝ) * ΔE) := by
      have hx :
          probPos (RingHom.id ℝ) p T s' u
            = 1 - logisticProb ((T.β : ℝ) * ΔE) := by
        simpa [hneg] using hbwdprob
      simp [hx]
    simp [hK_bwd, this]
  have hPratio :=
    boltzmann_ratio (NN:=NN) (spec:=spec) (p:=p) (T:=T) s s'
  have hPratio' :
      P s' / P s = Real.exp (-(T.β : ℝ) * ΔE) := by
    simpa [ΔE, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hPratio
  have hKratio :
      K (u:=u) s s' / K (u:=u) s' s
        = Real.exp (-(T.β : ℝ) * ΔE) := by
    have := logistic_ratio ((T.β : ℝ) * ΔE)
    simpa [hKf, hKb] using this
  have hKpos : 0 < K (u:=u) s' s := by
    simp [hKb, logisticProb_pos']
  have hPpos : 0 < P s := by
    classical
    have _ : IsHamiltonian (U:=U) (σ:=σ) NN :=
      IsHamiltonian_of_EnergySpec' (NN:=NN) (spec:=spec)
    set 𝓒 := CEparams (NN:=NN) (spec:=spec) p
    have instFin : 𝓒.IsFinite := by
      dsimp [𝓒, CEparams]; infer_instance
    unfold HopfieldBoltzmann.P
    simp only [HopfieldBoltzmann.CEparams]
    unfold CanonicalEnsemble.probability
    set Z := 𝓒.mathematicalPartitionFunction T
    have hZpos := mathematicalPartitionFunction_pos_finite (𝓒:=𝓒) (T:=T)
    have hExpPos : 0 < Real.exp (-(T.β : ℝ) * 𝓒.energy s) := Real.exp_pos _
    have : 0 < Real.exp (-(T.β : ℝ) * 𝓒.energy s) / Z := by
      exact div_pos hExpPos hZpos
    simpa [Z] using this
  exact detailed_balance_from_opposite_ratios
          (Pfun:=P) (Kfun:=fun a b => K (u:=u) a b)
          (s:=s) (s':=s') (β:=T.β) (ΔE:=ΔE)
          hPratio' hKratio hPpos hKpos

omit [Nonempty U] in
/-- Symmetric orientation (pos→neg) obtained from `detailed_balance_neg_pos` by swapping `s,s'`. -/
lemma detailed_balance_pos_neg
    {u : U} {s s' : NN.State}
    (h_off : ∀ v ≠ u, s.act v = s'.act v)
    (h_pos : s.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN))
    (h_neg : s'.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN)) :
    P s * K (u:=u) s s' = P s' * K (u:=u) s' s := by
  classical
  have hswap :=
    detailed_balance_neg_pos (NN:=NN) (spec:=spec) (p:=p) (T:=T)
      (u:=u) (s:=s') (s':=s)
      (h_off:=by
        intro v hv
        simp [h_off v hv])
      (h_neg:=h_neg) (h_pos:=h_pos)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hswap.symm

omit [Nonempty U] in
/--
**Theorem: Detailed Balance Condition (Reversibility)**.
The Gibbs update kernel satisfies the detailed balance condition with respect to the Boltzmann distribution.
P(s) K(s→s') = P(s') K(s'→s).
-/
theorem detailed_balance
    (u : U) (s s' : NN.State) :
    P s * K (u:=u) s s'
      = P s' * K (u:=u) s' s := by
  classical
  by_cases hDiff : DiffAway (NN:=NN) u s s'
  · exact detailed_balance_diffAway (NN:=NN) (spec:=spec) (p:=p) (T:=T) hDiff
  have h_off : ∀ v ≠ u, s.act v = s'.act v := by
    intro v hv
    by_contra H
    exact hDiff ⟨v, hv, H⟩
  by_cases hEq : s = s'
  · subst hEq; simp
  have hClass :=
    single_site_cases (NN:=NN) (u:=u) (s:=s) (s':=s') h_off hEq
  rcases hClass with hCase | hCase
  · rcases hCase with ⟨hpos, hneg⟩
    exact detailed_balance_pos_neg (NN:=NN) (spec:=spec) (p:=p) (T:=T)
      (u:=u) (s:=s) (s':=s') h_off hpos hneg
  · rcases hCase with ⟨hneg, hpos⟩
    exact detailed_balance_neg_pos (NN:=NN) (spec:=spec) (p:=p) (T:=T)
      (u:=u) (s:=s) (s':=s') h_off hneg hpos


end DetailedBalance

variable [Fintype ι] [DecidableEq ι] [Ring R] --[CommRing R]
open CanonicalEnsemble Constants

section DetailedBalance
open scoped Classical ENNReal Temperature Constants
open TwoState Temperature HopfieldBoltzmann ProbabilityTheory

variable {U σ : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (NN : NeuralNetwork ℝ U σ) [Fintype NN.State] [Nonempty NN.State]
variable [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
variable (spec : TwoState.EnergySpec' (NN:=NN))
variable (p : Params NN) (T : Temperature)

/-- Lift a family of PMFs to a Markov kernel on a finite (hence countable) state space.
We reuse `Kernel.ofFunOfCountable`, which supplies the measurability proof. -/
noncomputable def pmfToKernel
    {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (K : α → PMF α) :
    Kernel α α :=
  Kernel.ofFunOfCountable (fun a => (K a).toMeasure)

/-- Single–site Gibbs kernel at site `u` as a Kernel (uses existing `gibbsUpdate`).
`spec` is not needed here, so we underscore it to silence the unused-variable linter. -/
noncomputable def singleSiteKernel
    (NN : NeuralNetwork ℝ U σ) [Fintype NN.State] [DecidableEq U]
    [MeasurableSpace NN.State] [MeasurableSingletonClass NN.State]
    [TwoStateNeuralNetwork NN]
    (_spec : TwoState.EnergySpec' (NN:=NN)) (p : Params NN) (T : Temperature) (u : U) :
    Kernel NN.State NN.State :=
  pmfToKernel (fun s => TwoState.gibbsUpdate (NN:=NN) (RingHom.id ℝ) p T s u)

/-- Random–scan Gibbs kernel as uniform mixture over sites.
`spec` is likewise unused in the construction of the kernel itself. -/
noncomputable def randomScanKernel
    (NN : NeuralNetwork ℝ U σ) [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype NN.State] [DecidableEq NN.State] [MeasurableSpace NN.State] [MeasurableSingletonClass NN.State]
    [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
    (_spec : TwoState.EnergySpec' (NN:=NN)) (p : Params NN) (T : Temperature) :
    Kernel NN.State NN.State :=
  let sitePMF : PMF U := PMF.uniformOfFintype _
  pmfToKernel (fun s =>
    sitePMF.bind (fun u =>
      TwoState.gibbsUpdate (NN:=NN) (RingHom.id ℝ) p T s u))

section FiniteMeasureAPI
open scoped Classical
open MeasureTheory

variable {α : Type*}

/-- On a finite discrete measurable space (⊤ σ–algebra), every set is measurable. -/
@[simp] lemma measurableSet_univ_of_fintype
    [Fintype α] [MeasurableSpace α] (hσ : ‹MeasurableSpace α› = ⊤)
    (s : Set α) : MeasurableSet s := by
  subst hσ; trivial

/-- For a finite type with counting measure, the (lower) integral
is the finite sum (specialization of the `tsum` version).

FIX: Added `[MeasurableSingletonClass α]` which is required by `MeasureTheory.lintegral_count`.
Removed the auxiliary restricted / probability-specialized lemmas that caused build errors
(`lintegral_count_restrict`, `lintegral_fintype_prob_restrict`, `lintegral_restrict_as_sum_if`)
since they were unused and referenced a non‑existent lemma. -/
lemma lintegral_count_fintype
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [DecidableEq α]
    (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂(Measure.count : Measure α) = ∑ x : α, f x := by
  classical
  simpa [tsum_fintype] using (MeasureTheory.lintegral_count f)

-- Finite-type restricted lintegral as a weighted finite sum (separated lemma).
lemma lintegral_fintype_measure_restrict
    {α : Type*}
    [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (A : Set α) --(hA : MeasurableSet A)
    (f : α → ℝ≥0∞) :
    ∫⁻ x in A, f x ∂μ
      = ∑ x : α, (if x ∈ A then μ {x} * f x else 0) := by
  classical
  have hRestr :
      ∫⁻ x in A, f x ∂μ
        = ∑ x : α, f x * (μ.restrict A) {x} := by
    simpa using (lintegral_fintype (μ:=μ.restrict A) (f:=f))
  have hSingleton :
      ∀ x : α, (μ.restrict A) {x} = (if x ∈ A then μ {x} else 0) := by
    intro x
    by_cases hx : x ∈ A
    · have hInter : ({x} : Set α) ∩ A = {x} := by
        ext y; constructor
        · intro hy; rcases hy with ⟨hy1, hy2⟩
          simp at hy1
          subst hy1
          simp [hx]
        · intro hy
          simp [hy, hx]
          aesop
      simp [Measure.restrict_apply, hx, hInter]
    · have hInter : ({x} : Set α) ∩ A = (∅ : Set α) := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro y hy
        rcases hy with ⟨hy1, hy2⟩
        have : y = x := by simpa [Set.mem_singleton_iff] using hy1
        subst this
        exact hx hy2
      simp [Measure.restrict_apply, hx, hInter]
  calc
    ∫⁻ x in A, f x ∂μ
        = ∑ x : α, f x * (μ.restrict A) {x} := hRestr
    _ = ∑ x : α, f x * (if x ∈ A then μ {x} else 0) := by
          simp [hSingleton]
    _ = ∑ x : α, (if x ∈ A then μ {x} * f x else 0) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          by_cases hx : x ∈ A
          · simp [hx, mul_comm]
          · simp [hx]

/-- Probability measure style formula for a finite type:
turn a restricted integral into a finite sum with point masses. -/
lemma lintegral_fintype_prob_restrict
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (A : Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x in A, f x ∂μ
      = ∑ x : α, (if x ∈ A then μ {x} * f x else 0) := by
  simpa using lintegral_fintype_measure_restrict μ A f

/-- Restricted version over the counting measure (finite type).
Uses the probability-style formula specialized to `Measure.count`. -/
lemma lintegral_count_restrict
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α] [DecidableEq α]
    (A : Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x in A, f x ∂(Measure.count : Measure α)
      = ∑ x : α, (if x ∈ A then f x else 0) := by
  classical
  have h :=
    lintegral_fintype_prob_restrict (μ:=(Measure.count : Measure α)) A f
  have hμ : ∀ x : α, (Measure.count : Measure α) {x} = 1 := by
    intro x; simp
  simpa [hμ, one_mul] using h

/-- Convenience rewriting for the specific pattern used in detailed balance proofs:
move `μ {x}` factor to the left of function argument. -/
lemma lintegral_restrict_as_sum_if
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (A : Set α)
    (g : α → ℝ≥0∞) :
    ∫⁻ x in A, g x ∂μ
      = ∑ x : α, (if x ∈ A then μ {x} * g x else 0) :=
  lintegral_fintype_measure_restrict μ A g

end FiniteMeasureAPI

open MeasureTheory Set Finset Kernel TwoState HopfieldBoltzmann

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- (Helper) Every subset of a finite type is finite. -/
lemma Set.finite_of_subsingleton_fintype
    {γ : Type*} [Fintype γ] (S : Set γ) : S.Finite :=
  (Set.toFinite _)

namespace ProbabilityTheory
namespace Kernel

/-- Evaluation lemma for `Kernel.ofFunOfCountable`. Added for convenient rewriting/simp. -/
@[simp]
lemma ofFunOfCountable_apply
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α]
    (f : α → Measure β) (a : α) :
    (Kernel.ofFunOfCountable f) a = f a := rfl

end Kernel
end ProbabilityTheory

namespace ProbabilityTheory

open scoped Classical
open MeasureTheory

variable {U σ : Type}
variable {NN : NeuralNetwork ℝ U σ} [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
variable {spec : TwoState.EnergySpec' (NN:=NN)}
variable {p : Params NN} {T : Temperature}

section AuxFiniteSum

/-- General finite-type identity:
a sum over the whole type with an `if … ∈ S` guard can be rewritten
as a sum over the `Finset` of the elements that satisfy the guard. -/
lemma Finset.sum_if_mem_eq_sum_filter
    {α β : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid β]
    (S : Set α) (f : α → β) :
    (∑ x : α, (if x ∈ S then f x else 0))
      = ∑ x ∈ S.toFinset, f x := by
  classical
  have h_univ :
      (∑ x : α, (if x ∈ S then f x else 0))
        = ∑ x ∈ (Finset.univ : Finset α), (if x ∈ S then f x else 0) := by
    simp
  have h_filter :
      (∑ x ∈ (Finset.univ : Finset α), (if x ∈ S then f x else 0))
        = ∑ x ∈ (Finset.univ.filter fun x : α => x ∈ S), f x := by
    simpa using
      (Finset.sum_filter
          (s := (Finset.univ : Finset α))
          (p := fun x : α => x ∈ S)
          (f := f)).symm
  have h_ident :
      (Finset.univ.filter fun x : α => x ∈ S) = S.toFinset := by
    ext x
    by_cases hx : x ∈ S
    · simp [hx, Finset.mem_filter, Set.mem_toFinset]
    · simp [hx, Finset.mem_filter, Set.mem_toFinset]
  simp [h_univ, h_filter, h_ident]

lemma Finset.sum_subset_of_subset
    {α β : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid β]
    (S : Set α) (f : α → β)
    (_h₁ : ∀ x, x ∈ S.toFinset → True)
    (_h₂ : ∀ x, x ∈ S.toFinset → False → False)
    (_h₃ : ∀ x, x ∈ S.toFinset → True) :
    (∑ x : α, (if x ∈ S then f x else 0))
      = ∑ x ∈ S.toFinset, f x :=
  Finset.sum_if_mem_eq_sum_filter S f

end AuxFiniteSum

/-- Uniform random-scan kernel evaluation:
the kernel probability of a measurable set `B` equals the arithmetic
average of the single-site kernel probabilities. -/
lemma randomScanKernel_eval_uniform
    {U σ : Type} [Fintype U] [DecidableEq U] [Nonempty U]
    {NN : NeuralNetwork ℝ U σ}
    [Fintype NN.State] [DecidableEq NN.State]
    [MeasurableSpace NN.State] [MeasurableSingletonClass NN.State]
    [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
    (spec : TwoState.EnergySpec' (NN:=NN))
    (p : Params NN) (T : Temperature)
    (x : NN.State) (B : Set NN.State) (_ : MeasurableSet B) :
    (randomScanKernel (NN:=NN) spec p T) x B
      =
    (∑ u : U, (singleSiteKernel (NN:=NN) spec p T u) x B)
/ (Fintype.card U : ℝ≥0∞) := by
  classical
  unfold randomScanKernel singleSiteKernel pmfToKernel
  simp [Kernel.ofFunOfCountable, Kernel.ofFunOfCountable_apply]
  let sitePMF := PMF.uniformOfFintype U
  let g : U → PMF NN.State :=
    fun u ↦ TwoState.gibbsUpdate (NN:=NN) (RingHom.id ℝ) p T x u
  have hConst :
      (sitePMF.bind g).toMeasure B
        =
      (∑ u : U, (g u).toMeasure B)
/ (Fintype.card U : ℝ≥0∞) := by
    classical
    have hμ : ∀ u : U, sitePMF u = (Fintype.card U : ℝ≥0∞)⁻¹ := by
      intro u; simp [sitePMF, PMF.uniformOfFintype_apply]
    simp [PMF.toMeasure_apply, tsum_fintype, PMF.bind_apply, hμ,
          Finset.mul_sum, Finset.sum_mul, Finset.sum_comm,
          ENNReal.div_eq_inv_mul, Set.indicator_apply,
          mul_comm, mul_left_comm, mul_assoc] at *
  aesop

end ProbabilityTheory

/-- On a finite (any finite subset) space with measurable singletons, the measure of a finite
set under a kernel is the finite sum of the singleton masses. (Refactored: Finset induction;
avoids problematic `hB.induction_on` elaboration.) -/
lemma Kernel.measure_eq_sum_finset
    [DecidableEq α] [MeasurableSingletonClass α]
    (κ : Kernel β α) (x : β) {B : Set α} (hB : B.Finite) :
    κ x B = ∑ y ∈ hB.toFinset, κ x {y} := by
  classical
  have hBset : B = (hB.toFinset : Finset α).toSet := by
    ext a; aesop
  set s : Finset α := hB.toFinset
  suffices H : κ x s.toSet = ∑ y ∈ s, κ x {y} by aesop
  refine s.induction_on ?h0 ?hstep
  · simp
  · intro a s ha_notin hIH
    have hDisj : Disjoint ({a} : Set α) s.toSet := by
      refine disjoint_left.mpr ?_
      intro y hy_in hy_in_s
      have : y = a := by simpa using hy_in
      subst this
      aesop
    have hMeas_s : MeasurableSet s.toSet := by
      refine s.induction_on ?m0 ?mstep
      · simp
      · intro b t hb_notin ht
        simpa [Finset.coe_insert, Set.image_eq_range, Set.union_comm, Set.union_left_comm,
               Set.union_assoc] using (ht.union (measurableSet_singleton b))
    have hMeas_a : MeasurableSet ({a} : Set α) := measurableSet_singleton a
    have hUnion :
        (insert a s).toSet
          = ({a} : Set α) ∪ s.toSet := by
      ext y; by_cases hy : y = a
      · subst hy; simp
      · simp [hy]
    have hAdd :
        κ x ((insert a s).toSet)
          = κ x ({a} : Set α) + κ x s.toSet := by
      rw [← measure_union_add_inter {a} hMeas_s]
      simp_rw [hUnion, measure_union_add_inter {a} hMeas_s]
      exact measure_union hDisj hMeas_s
    have hSum :
        ∑ y ∈ insert a s, κ x {y}
          = κ x ({a} : Set α) + ∑ y ∈ s, κ x {y} := by
      simp [Finset.sum_insert, ha_notin]
    calc
      κ x ((insert a s).toSet)
          = κ x ({a} : Set α) + κ x s.toSet := hAdd
      _ = κ x ({a} : Set α) + ∑ y ∈ s, κ x {y} := by rw [hIH]
      _ = ∑ y ∈ insert a s, κ x {y} := by simp [hSum]

omit [Fintype U] [DecidableEq U] [Nonempty U] in
lemma lintegral_randomScanKernel_as_sum_div
    (NN : NeuralNetwork ℝ U σ) [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype NN.State] [DecidableEq NN.State]
    [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
    (spec : TwoState.EnergySpec' (NN:=NN))
    (p : Params NN) (T : Temperature)
    (π : Measure (NN.State))
    (A B : Set NN.State) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ x in A, (randomScanKernel (NN:=NN) spec p T) x B ∂π
      =
    (∑ u : U,
        ∫⁻ x in A, (singleSiteKernel (NN:=NN) spec p T u) x B ∂π)
/ (Fintype.card U : ℝ≥0∞) := by
  classical
  letI : MeasurableSpace NN.State := ⊤
  letI : MeasurableSingletonClass NN.State := ⟨fun _ => trivial⟩
  set κ := randomScanKernel (NN:=NN) spec p T
  set κu := fun u : U => singleSiteKernel (NN:=NN) spec p T u
  set c : ℝ≥0∞ := (Fintype.card U : ℝ≥0∞)⁻¹ with hc
  have h_div : (↑(Fintype.card U) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card U ≠ 0)
  have hEval :
      ∀ x, κ x B = c * ∑ u : U, (κu u) x B := by
    intro x
    have hx :=
      randomScanKernel_eval_uniform (NN:=NN) (spec:=spec) p T x B hB
    simp [κ, κu, c, ENNReal.div_eq_inv_mul, hx, mul_comm, mul_left_comm, mul_assoc]
  have hLHS :
      ∫⁻ x in A, κ x B ∂π
        = c * ∑ u : U, ∫⁻ x in A, (κu u) x B ∂π := by
    have hEval' :
        (fun x => κ x B) =
          fun x => c * ∑ u : U, (κu u) x B := by
      funext x; simp [hEval x]
    calc
      ∫⁻ x in A, κ x B ∂π
          = ∫⁻ x in A, c * (∑ u : U, (κu u) x B) ∂π := by
              simp [hEval', mul_comm, mul_left_comm, mul_assoc]
      _ = c * ∫⁻ x in A, (∑ u : U, (κu u) x B) ∂π := by
              erw [← lintegral_const_mul c fun ⦃t⦄ a => _]
              exact fun ⦃t⦄ a => hA
      _ = c * ∑ u : U, ∫⁻ x in A, (κu u) x B ∂π := by
              have :
                  ∫⁻ x in A, (∑ u : U, (κu u) x B) ∂π
                    = ∑ u : U, ∫⁻ x in A, (κu u) x B ∂π := by
                  erw [lintegral_finset_sum Finset.univ fun b a ⦃t⦄ a => _]
                  exact fun b a ⦃t⦄ a => hA
              simpa using congrArg (fun z => c * z) this
  have hRHS :
      (∑ u : U, ∫⁻ x in A, (κu u) x B ∂π)
/ (Fintype.card U : ℝ≥0∞)
        = c * ∑ u : U, ∫⁻ x in A, (κu u) x B ∂π := by
    rw [ENNReal.div_eq_inv_mul]
  aesop

omit [Fintype U] [DecidableEq U] [Nonempty U] in
/-- Averaging lemma: uniform average of reversible single–site kernels is reversible. -/
lemma randomScanKernel_reversible_of_sites
    (NN : NeuralNetwork ℝ U σ) [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype NN.State] [DecidableEq NN.State]
    [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
    (spec : TwoState.EnergySpec' (NN:=NN))
    (p : Params NN) (T : Temperature)
    (π : Measure (NN.State))
    (hSite :
      ∀ u, ProbabilityTheory.Kernel.IsReversible
              (singleSiteKernel (NN:=NN) spec p T u) π) :
    ProbabilityTheory.Kernel.IsReversible
      (randomScanKernel (NN:=NN) spec p T) π := by
  classical
  letI : MeasurableSpace NN.State := ⊤
  letI : MeasurableSingletonClass NN.State := ⟨fun _ => trivial⟩
  intro A B hA hB
  have hSum :
      (∑ u : U,
          ∫⁻ x in A, (singleSiteKernel (NN:=NN) spec p T u) x B ∂π)
        =
      (∑ u : U,
          ∫⁻ x in B, (singleSiteKernel (NN:=NN) spec p T u) x A ∂π) := by
    refine Finset.sum_congr rfl ?_
    intro u _; exact hSite u hA hA
  have hAexpr :=
    lintegral_randomScanKernel_as_sum_div (NN:=NN) (spec:=spec) p T π A B hA hB
  have hBexpr :=
    lintegral_randomScanKernel_as_sum_div (NN:=NN) (spec:=spec) p T π B A hB hA
  simp [hAexpr, hBexpr, hSum]

section ReversibilityFinite

open scoped Classical
open MeasureTheory

variable {α : Type*}
variable [Fintype α] [DecidableEq α]
variable [MeasurableSpace α] [MeasurableSingletonClass α]
variable (π : Measure α) (κ : Kernel α α)

/-- Finite discrete expansion of a restricted lintegral of a kernel (measurable singletons). -/
lemma lintegral_kernel_restrict_fintype
    (A : Set α) :
    ∫⁻ x in A, κ x A ∂π
      =
    ∑ x : α, (if x ∈ A then π {x} * κ x A else 0) := by
  classical
  simpa using
    (lintegral_restrict_as_sum_if (μ:=π) (A:=A) (g:=fun x => κ x A))

/-- Finite discrete reversibility from pointwise detailed balance. -/
lemma Kernel.isReversible_of_pointwise_fintype
    (hPoint :
      ∀ ⦃x y⦄, π {x} * κ x {y} = π {y} * κ y {x})
    : ProbabilityTheory.Kernel.IsReversible κ π := by
  classical
  intro A B hA hB
  have hFinA : A.Finite := Set.finite_of_subsingleton_fintype A
  have hFinB : B.Finite := Set.finite_of_subsingleton_fintype B
  have hAexp :
      ∫⁻ x in A, κ x B ∂π
        = ∑ x ∈ hFinA.toFinset, π {x} * κ x B := by
    have h1 :
        ∫⁻ x in A, κ x B ∂π
          = ∑ x : α,
              (if x ∈ A then π {x} * κ x B else 0) := by
      simpa using
        (lintegral_restrict_as_sum_if (μ:=π) (A:=A) (g:=fun x => κ x B))
    have :
        (∑ x : α, (if x ∈ A then π {x} * κ x B else 0))
          =
        ∑ x ∈ hFinA.toFinset, π {x} * κ x B := by
      classical
      simp_rw
        [(ProbabilityTheory.Finset.sum_if_mem_eq_sum_filter
            (S:=A) (f:=fun x => π {x} * κ x B))]
      rw [@toFinite_toFinset]
    simp [h1, this]
  have hBexp :
      ∫⁻ x in B, κ x A ∂π
        = ∑ x ∈ hFinB.toFinset, π {x} * κ x A := by
    have h1 :
        ∫⁻ x in B, κ x A ∂π
          = ∑ x : α,
              (if x ∈ B then π {x} * κ x A else 0) := by
      simpa using
        (lintegral_restrict_as_sum_if (μ:=π) (A:=B) (g:=fun x => κ x A))
    have :
        (∑ x : α, (if x ∈ B then π {x} * κ x A else 0))
          =
        ∑ x ∈ hFinB.toFinset, π {x} * κ x A := by
      classical
      simp_rw
        [(ProbabilityTheory.Finset.sum_if_mem_eq_sum_filter
            (S:=B) (f:=fun x => π {x} * κ x A))]
      rw [@toFinite_toFinset]
    simp [h1, this]
  have hκB :
      ∀ x, κ x B = ∑ y ∈ hFinB.toFinset, κ x {y} := by
    intro x; simpa using
      (Kernel.measure_eq_sum_finset (κ:=κ) x hFinB)
  have hκA :
      ∀ x, κ x A = ∑ y ∈ hFinA.toFinset, κ x {y} := by
    intro x; simpa using
      (Kernel.measure_eq_sum_finset (κ:=κ) x hFinA)
  have hL :
      ∑ x ∈ hFinA.toFinset, π {x} * κ x B
        =
      ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {x} * κ x {y} := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp_rw [hκB x, Finset.mul_sum]
  have hR :
      ∑ x ∈ hFinB.toFinset, π {x} * κ x A
        =
      ∑ x ∈ hFinB.toFinset, ∑ y ∈ hFinA.toFinset, π {x} * κ x {y} := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp_rw [hκA x, Finset.mul_sum]
  erw [hAexp, hBexp, hL, hR]
  have hRew :
      ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {x} * κ x {y}
        =
      ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {y} * κ y {x} := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    refine Finset.sum_congr rfl ?_
    intro y hy
    exact hPoint (x:=x) (y:=y)
  calc
      ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {x} * κ x {y}
          = ∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset, π {y} * κ y {x} := hRew
      _ = ∑ y ∈ hFinB.toFinset, ∑ x ∈ hFinA.toFinset, π {y} * κ y {x} := by
            simpa using
              (Finset.sum_comm :
                (∑ x ∈ hFinA.toFinset, ∑ y ∈ hFinB.toFinset,
                    π {y} * κ y {x})
                  =
                ∑ y ∈ hFinB.toFinset, ∑ x ∈ hFinA.toFinset,
                    π {y} * κ y {x})
      _ = ∑ x ∈ hFinB.toFinset, ∑ y ∈ hFinA.toFinset, π {x} * κ x {y} := rfl

end ReversibilityFinite

/-- Singleton evaluation of a PMF turned into a measure. -/
@[simp]
lemma PMF.toMeasure_singleton
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (a : α) :
    p.toMeasure {a} = p a := by
  rw [toMeasure_apply_eq_toOuterMeasure, toOuterMeasure_apply_singleton]

-- ## Single–site pointwise detailed balance (finite two–state Hopfield)

section SingleSitePointwise

open scoped Classical ENNReal
open MeasureTheory TwoState HopfieldBoltzmann ProbabilityTheory

variable {U σ : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (NN : NeuralNetwork ℝ U σ)
variable [Fintype NN.State] [DecidableEq NN.State] [Nonempty NN.State]
variable [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
variable (spec : TwoState.EnergySpec' (NN:=NN))
variable (p : Params NN) (T : Temperature)

/-- Helper: canonical Boltzmann measure we use below. -/
private noncomputable abbrev πBoltz : Measure NN.State :=
  (HopfieldBoltzmann.CEparams (NN:=NN) (spec:=spec) p).μProd T

omit [Fintype U] [Nonempty U] [DecidableEq NN.State] [Nonempty NN.State] [TwoStateExclusive NN] in
/-- Evaluation of the single–site Gibbs kernel on a singleton. -/
lemma singleSiteKernel_singleton_eval
    (u : U) (s t : NN.State) :
    (singleSiteKernel (NN:=NN) spec p T u) s {t}
      = ENNReal.ofReal (HopfieldBoltzmann.Kbm (NN:=NN) p T u s t) := by
  classical
  letI : MeasurableSpace NN.State := ⊤
  letI : MeasurableSingletonClass NN.State := ⟨fun _ => trivial⟩
  have hPMF :
      (singleSiteKernel (NN:=NN) spec p T u) s {t}
        =
      (TwoState.gibbsUpdate (NN:=NN) (RingHom.id ℝ) p T s u) t := by
    unfold singleSiteKernel pmfToKernel
    simp_rw [Kernel.ofFunOfCountable_apply, PMF.toMeasure_singleton]
  have hfin :
      (TwoState.gibbsUpdate (NN:=NN) (RingHom.id ℝ) p T s u) t ≠ (⊤ : ℝ≥0∞) := by
    have hle :
        (TwoState.gibbsUpdate (NN:=NN) (RingHom.id ℝ) p T s u) t ≤ 1 := by
      simpa using
        (TwoState.gibbsUpdate (NN:=NN) (RingHom.id ℝ) p T s u).coe_le_one t
    have hlt : (TwoState.gibbsUpdate (NN:=NN) (RingHom.id ℝ) p T s u) t
                < (⊤ : ℝ≥0∞) :=
      lt_of_le_of_lt hle (by simp)
    exact (ne_of_lt hlt)
  calc
    (singleSiteKernel (NN:=NN) spec p T u) s {t}
        = (TwoState.gibbsUpdate (NN:=NN) (RingHom.id ℝ) p T s u) t := hPMF
    _ = ENNReal.ofReal ((TwoState.gibbsUpdate (NN:=NN) (RingHom.id ℝ) p T s u) t).toReal := by
          simp [ENNReal.ofReal_toReal, hfin]
    _ = ENNReal.ofReal (HopfieldBoltzmann.Kbm (NN:=NN) p T u s t) := rfl

omit [Nonempty U] [DecidableEq NN.State] in
/-- Evaluation of the Boltzmann measure on a singleton as `ofReal` of the Boltzmann probability. -/
lemma boltzmann_singleton_eval
    (s : NN.State) :
    (πBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T)) {s}
      =
    ENNReal.ofReal (HopfieldBoltzmann.P (NN:=NN) (spec:=spec) p T s) := by
  classical
  have _ : IsHamiltonian (U:=U) (σ:=σ) NN :=
    IsHamiltonian_of_EnergySpec' (NN:=NN) (spec:=spec)
  have : (HopfieldBoltzmann.CEparams (NN:=NN) (spec:=spec) p).μProd T {s}
        =
      ENNReal.ofReal
        ((HopfieldBoltzmann.CEparams (NN:=NN) (spec:=spec) p).probability T s) := by
    simp
  simp [πBoltz, HopfieldBoltzmann.P, HopfieldBoltzmann.CEparams]

omit [Nonempty U] [DecidableEq NN.State] in
lemma singleSite_pointwise_detailed_balance
    (u : U) :
    ∀ s t : NN.State,
      (πBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T)) {s}
        * (singleSiteKernel (NN:=NN) spec p T u) s {t}
        =
      (πBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T)) {t}
        * (singleSiteKernel (NN:=NN) spec p T u) t {s} := by
  classical
  intro s t
  have hReal :=
    detailed_balance (NN:=NN) (spec:=spec) (p:=p) (T:=T) (u:=u) s t
  have hπs := boltzmann_singleton_eval (NN:=NN) (spec:=spec) (p:=p) (T:=T) s
  have hπt := boltzmann_singleton_eval (NN:=NN) (spec:=spec) (p:=p) (T:=T) t
  have hκst :=
    singleSiteKernel_singleton_eval (NN:=NN) (spec:=spec) (p:=p) (T:=T) u s t
  have hκts :=
    singleSiteKernel_singleton_eval (NN:=NN) (spec:=spec) (p:=p) (T:=T) u t s
  have hPs_nonneg :
      0 ≤ HopfieldBoltzmann.P (NN:=NN) (spec:=spec) p T s := by
    have _ : IsHamiltonian (U:=U) (σ:=σ) NN :=
      IsHamiltonian_of_EnergySpec' (NN:=NN) (spec:=spec)
    exact probability_nonneg_finite
      (𝓒:=HopfieldBoltzmann.CEparams (NN:=NN) (spec:=spec) p) (T:=T) (i:=s)
  have hPt_nonneg :
      0 ≤ HopfieldBoltzmann.P (NN:=NN) (spec:=spec) p T t := by
    have _ : IsHamiltonian (U:=U) (σ:=σ) NN :=
      IsHamiltonian_of_EnergySpec' (NN:=NN) (spec:=spec)
    exact probability_nonneg_finite
      (𝓒:=HopfieldBoltzmann.CEparams (NN:=NN) (spec:=spec) p) (T:=T) (i:=t)
  have hKst_nonneg :
      0 ≤ HopfieldBoltzmann.Kbm (NN:=NN) p T u s t := by
    unfold HopfieldBoltzmann.Kbm; exact ENNReal.toReal_nonneg
  have hKts_nonneg :
      0 ≤ HopfieldBoltzmann.Kbm (NN:=NN) p T u t s := by
    unfold HopfieldBoltzmann.Kbm; exact ENNReal.toReal_nonneg
  rw [hπs, hπt, hκst, hκts,
      ← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul, hReal]
  all_goals
    first
      | exact mul_nonneg hPs_nonneg hKst_nonneg
      | simp_all only [μProd_singleton_of_fintype]

omit [Nonempty U] in
/-- Reversibility of the single–site kernel w.r.t. the Boltzmann measure (patched). -/
lemma singleSiteKernel_reversible
    (u : U) :
    ProbabilityTheory.Kernel.IsReversible
      (singleSiteKernel (NN:=NN) spec p T u)
      (πBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T)) := by
  classical
  letI : MeasurableSpace NN.State := ⊤
  letI : MeasurableSingletonClass NN.State := ⟨fun _ => trivial⟩
  refine Kernel.isReversible_of_pointwise_fintype
      (π:=πBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T))
      (κ:=singleSiteKernel (NN:=NN) spec p T u) ?_
  intro x y
  simpa using
    singleSite_pointwise_detailed_balance (NN:=NN) (spec:=spec) (p:=p) (T:=T) u x y

end SingleSitePointwise

section RandomScan

open scoped Classical
open MeasureTheory
open TwoState HopfieldBoltzmann ProbabilityTheory

variable {U σ : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (NN : NeuralNetwork ℝ U σ) [Fintype NN.State] [DecidableEq NN.State] [Nonempty NN.State]
variable [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
variable (spec : TwoState.EnergySpec' (NN:=NN))
variable (p : Params NN) (T : Temperature)

/-- Reversibility of the random–scan Gibbs kernel (uniform site choice) w.r.t. the Boltzmann measure. -/
theorem randomScanKernel_reversible :
    ProbabilityTheory.Kernel.IsReversible
      (randomScanKernel (NN:=NN) spec p T)
      ((HopfieldBoltzmann.CEparams (NN:=NN) (spec:=spec) p).μProd T) := by
  classical
  have hSite :
      ∀ u : U,
        ProbabilityTheory.Kernel.IsReversible
          (singleSiteKernel (NN:=NN) spec p T u)
          ((HopfieldBoltzmann.CEparams (NN:=NN) (spec:=spec) p).μProd T) := by
    intro u
    simpa [πBoltz,
           HopfieldBoltzmann.CEparams] using
      (singleSiteKernel_reversible (NN:=NN) (spec:=spec) (p:=p) (T:=T) u)
  exact
    randomScanKernel_reversible_of_sites
      (NN:=NN) (spec:=spec) (p:=p) (T:=T)
      ((HopfieldBoltzmann.CEparams (NN:=NN) (spec:=spec) p).μProd T)
      hSite

end RandomScan
