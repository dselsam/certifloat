-- TODO(dhs): need to do this over tensors, need multi-dimension relative errors

namespace real
constants (real : Type)
notation `ℝ` := real

axiom real_linear_ordered_field : linear_ordered_field real

noncomputable instance : linear_ordered_field real := real_linear_ordered_field

constants (sqrt : ℝ → ℝ)
axiom sqrt_mul (x y : ℝ) : sqrt (x * y) = sqrt x * sqrt y
axiom sqrt_one : sqrt 1 = 1

noncomputable def norm (x : ℝ) : ℝ := sqrt (x * x)
noncomputable def d (x y : ℝ) : ℝ := norm (x - y)
noncomputable def err (x y : ℝ) : ℝ := (d x y) / (norm y)

lemma norm_one : norm 1 = 1 := by simp [norm, sqrt_one]
lemma norm_ne_zero (x : ℝ) : x ≠ 0 → norm x ≠ 0 := sorry
lemma norm_norm (x : ℝ) : norm (norm x) = norm x := sorry
lemma norm_add (x y c : ℝ) : norm x + norm y ≤ c → norm (x + y) ≤ c := sorry
lemma le_add (x y c₁ c₂ : ℝ) : x ≤ c₁ → y ≤ c₂ → x + y ≤ c₁ + c₂ := sorry
lemma mul_le (x y c : ℝ) : x ≤ c → y ≤ c → norm c ≤ 1 → x * y ≤ c := sorry
lemma norm_add_le (x y c₁ c₂ : ℝ) : norm x ≤ c₁ → norm y ≤ c₂ → norm (x + y) ≤ (c₁ + c₂) :=
begin
intros H_x H_y,
apply norm_add,
apply le_add,
exact H_x,
exact H_y
end

lemma norm_mul (x y : ℝ) : norm (x * y) = norm x * norm y :=
calc  norm (x * y)
    = sqrt (x * x * y * y) : by simp [norm]
... = sqrt (x * x) * sqrt (y * y) : by simp [sqrt_mul]
... = norm x * norm y : rfl

axiom div_self_mul (x y : ℝ) (H_x : x ≠ 0) : x * y / x = y

lemma rel_err (x ε : ℝ) (H_x : norm x ≠ 0) : err (x * (1 + ε)) x = norm ε :=
calc  err (x * (1 + ε)) x
    = norm (x * (1 + ε) - x) / norm x : rfl
... = norm (x * ε) / norm x : by simp [left_distrib]
... = (norm x * norm ε) / norm x : by simp [norm_mul]
... = norm ε : by simp [div_self_mul _ _ H_x]

notation `|` x `|` := norm x
--notation `⟦` x `;` y `⟧` := err x y

def O₁ (f : ℝ → ℝ) : Prop :=
  ∃ (c : ℝ) (ε₀ : ℝ),
    ∀ (ε : ℝ),
      |ε| ≤ |ε₀| → |f ε| ≤ c * ε

end real
open real

namespace float
constants (fl ε_fl : ℝ → ℝ → ℝ)
          (add mul sub div : ℝ → ℝ → ℝ → ℝ)
          (ε_add ε_mul ε_sub ε_div : ℝ → ℝ → ℝ → ℝ)

axiom ε_fl_approx  : ∀ (ε_m x : ℝ),   fl  ε_m x   = x       * (1 + ε_fl ε_m x)
axiom ε_add_approx : ∀ (ε_m x y : ℝ), add ε_m x y = (x + y) * (1 + ε_add ε_m x y)
axiom ε_mul_approx : ∀ (ε_m x y : ℝ), mul ε_m x y = (x * y) * (1 + ε_mul ε_m x y)
axiom ε_sub_approx : ∀ (ε_m x y : ℝ), sub ε_m x y = (x - y) * (1 + ε_sub ε_m x y)
axiom ε_div_approx : ∀ (ε_m x y : ℝ), div ε_m x y = (x / y) * (1 + ε_div ε_m x y)

axiom ε_fl_small  : ∀ (ε_m x : ℝ),   |ε_fl  ε_m x|   ≤ ε_m
axiom ε_add_small : ∀ (ε_m x y : ℝ), |ε_add ε_m x y| ≤ ε_m
axiom ε_mul_small : ∀ (ε_m x y : ℝ), |ε_mul ε_m x y| ≤ ε_m
axiom ε_sub_small : ∀ (ε_m x y : ℝ), |ε_sub ε_m x y| ≤ ε_m
axiom ε_div_small : ∀ (ε_m x y : ℝ), |ε_div ε_m x y| ≤ ε_m

end float

namespace certifloat

-- TODO(dhs): fix once we use vectors/tensors
-- TODO(dhs): could weaken so it _almost_ equals the modified problem
def backwards_stable₂ (algorithm : ℝ → ℝ → ℝ → ℝ) (problem : ℝ → ℝ → ℝ) : Prop :=
  ∀ (x y : ℝ), x ≠ 0 → y ≠ 0 → ∃ (x₀ y₀ : ℝ → ℝ),
    (∀ (ε_m : ℝ), algorithm ε_m x y = problem (x₀ ε_m) (y₀ ε_m))
  ∧ O₁ (λ ε_m, err (x₀ ε_m) x) ∧ O₁ (λ ε_m, err (y₀ ε_m) y)

inductive op : Type
| add, mul, sub, div

namespace op

noncomputable def rdenote : op → (real → real → real)
| op.add x y := x + y
| op.mul x y := x * y
| op.sub x y := x - y
| op.div x y := x / y

attribute [simp] rdenote

noncomputable def fdenote : op → (real → real → real → real)
| op.add ε_m x y := float.add ε_m x y
| op.mul ε_m x y := float.mul ε_m x y
| op.sub ε_m x y := float.sub ε_m x y
| op.div ε_m x y := float.div ε_m x y

attribute [simp] fdenote

end op

inductive scalar_function₂ : Type
| input  : bool → scalar_function₂
| const  : ℝ → scalar_function₂
| node   : op → scalar_function₂ → scalar_function₂ → scalar_function₂

namespace scalar_function₂

noncomputable def rdenote : scalar_function₂ → ℝ → ℝ → ℝ
| (input b)       x₁ x₂ := if b then x₁ else x₂
| (const y)       x₁ x₂ := y
| (node op t₁ t₂) x₁ x₂ := op^.rdenote (rdenote t₁ x₁ x₂) (rdenote t₂ x₁ x₂)

attribute [simp] rdenote

noncomputable def fdenote (ε_m : ℝ) : scalar_function₂ → ℝ → ℝ → ℝ
| (input b)       x₁ x₂ := if b then float.fl ε_m x₁ else float.fl ε_m x₂
| (const y)       x₁ x₂ := float.fl ε_m y
| (node op t₁ t₂) x₁ x₂ := op^.fdenote ε_m (fdenote t₁ x₁ x₂) (fdenote t₂ x₁ x₂)

attribute [simp] fdenote

def is_backwards_stable₂ (f : scalar_function₂) : Prop :=
 backwards_stable₂ (λ (ε_m x₁ x₂ : ℝ), f^.fdenote ε_m x₁ x₂)
                   (λ (x₁ x₂ : ℝ), f^.rdenote x₁ x₂)

end scalar_function₂

namespace subtract
open scalar_function₂ float

def subtract : scalar_function₂ := node op.sub (input tt) (input ff)

noncomputable def x' (x y ε_m : ℝ) : ℝ :=
x * ((1 + ε_fl ε_m x) * (1 + ε_sub ε_m (x * (1 + ε_fl ε_m x)) (y * (1 + ε_fl ε_m y))))

noncomputable def y' (x y ε_m : ℝ) : ℝ :=
y * ((1 + ε_fl ε_m y) * (1 + ε_sub ε_m (x * (1 + ε_fl ε_m x)) (y * (1 + ε_fl ε_m y))))

lemma subtract_in_desired_form (ε_m x y : ℝ) :
  sub ε_m (fl ε_m x) (fl ε_m y) = x' x y ε_m - y' x y ε_m :=
calc  sub ε_m (fl ε_m x) (fl ε_m y)
    = sub ε_m (x * (1 + ε_fl ε_m x)) (y * (1 + ε_fl ε_m y)) : by simp [ε_fl_approx]
... = (x * (1 + ε_fl ε_m x) - y * (1 + ε_fl ε_m y)) * (1 + ε_sub ε_m (x * (1 + ε_fl ε_m x)) (y * (1 + ε_fl ε_m y))) : by simp [ε_sub_approx]
... = x * (1 + ε_fl ε_m x) * (1 + ε_sub ε_m (x * (1 + ε_fl ε_m x)) (y * (1 + ε_fl ε_m y)))
    - y * (1 + ε_fl ε_m y) * (1 + ε_sub ε_m (x * (1 + ε_fl ε_m x)) (y * (1 + ε_fl ε_m y))) : by simp [left_distrib, right_distrib]
... = x' x y ε_m - y' x y ε_m : by simp [x', y']

lemma x'_close_enough : ∀ (x y : ℝ), x ≠ 0 → O₁ (λ ε_m, err (x' x y ε_m) x) :=
begin
intros x y H_x,
dunfold O₁,
apply exists.intro (3 : ℝ),
simp,
dunfold x',
apply exists.intro (1 : ℝ),
intros ε_m,
intros H_ε_m_small,
let ε₁ : ℝ := ε_fl ε_m x,
let ε₂ : ℝ := ε_sub ε_m (x * (1 + ε_fl ε_m x)) (y * (1 + ε_fl ε_m y)),
change |err (x * ((1 + ε₁) * (1 + ε₂))) x| ≤ ε_m * 3,
let ε₃ : ℝ := ε₁ + ε₂ + ε₁ * ε₂,

have H : (x * ((1 + ε₁) * (1 + ε₂))) = x * (1 + ε₃) := by simp [left_distrib, right_distrib],
rw H, clear H,

rw rel_err,
rw norm_norm,

have H₁ : |ε₁| ≤ ε_m := by apply ε_fl_small,
have H₂ : |ε₂| ≤ ε_m := by apply ε_sub_small,
have H₁₂ : |ε₁ * ε₂| ≤ ε_m,
rw norm_mul,
apply mul_le,
exact H₁,
exact H₂,
rw norm_one at H_ε_m_small,
exact H_ε_m_small,

have H₃ : |ε₁ + ε₂ + ε₁ * ε₂| ≤ ε_m + ε_m + ε_m,

apply norm_add_le,
apply norm_add_le,
exact H₁,
exact H₂,
exact H₁₂,

have H : ε_m * 3 = ε_m + ε_m + ε_m := by simp [norm_num.mul_bit0, norm_num.mul_bit1, bit0],
rw H, clear H,
exact H₃,

apply norm_ne_zero,
exact H_x
end

lemma y'_close_enough : ∀ (x y : ℝ), y ≠ 0 → O₁ (λ ε_m, err (y' x y ε_m) y) :=
begin
intros x y H_y,
dunfold O₁,
apply exists.intro (3 : ℝ),
simp,
dunfold y',
apply exists.intro (1 : ℝ),
intros ε_m,
intros H_ε_m_small,
let ε₁ : ℝ := ε_fl ε_m y,
let ε₂ : ℝ := ε_sub ε_m (x * (1 + ε_fl ε_m x)) (y * (1 + ε_fl ε_m y)),
change |err (y * ((1 + ε₁) * (1 + ε₂))) y| ≤ ε_m * 3,
let ε₃ : ℝ := ε₁ + ε₂ + ε₁ * ε₂,

have H : (y * ((1 + ε₁) * (1 + ε₂))) = y * (1 + ε₃) := by simp [left_distrib, right_distrib],
rw H, clear H,

rw rel_err,
rw norm_norm,

have H₁ : |ε₁| ≤ ε_m := by apply ε_fl_small,
have H₂ : |ε₂| ≤ ε_m := by apply ε_sub_small,
have H₁₂ : |ε₁ * ε₂| ≤ ε_m,
rw norm_mul,
apply mul_le,
exact H₁,
exact H₂,
rw norm_one at H_ε_m_small,
exact H_ε_m_small,

have H₃ : |ε₁ + ε₂ + ε₁ * ε₂| ≤ ε_m + ε_m + ε_m,

apply norm_add_le,
apply norm_add_le,
exact H₁,
exact H₂,
exact H₁₂,

have H : ε_m * 3 = ε_m + ε_m + ε_m := by simp [norm_num.mul_bit0, norm_num.mul_bit1, bit0],
rw H, clear H,
exact H₃,

apply norm_ne_zero,
exact H_y
end

theorem subtract_backwards_stable : is_backwards_stable₂ subtract :=
begin
dunfold is_backwards_stable₂ backwards_stable₂,
intros x y H_x H_y,
eapply exists.intro (x' x y),
eapply exists.intro (y' x y),
split,
{ intro ε_m, apply subtract_in_desired_form },
split,
{ apply x'_close_enough _ _ H_x },
{ apply y'_close_enough _ _ H_y },
end

end subtract
end certifloat
