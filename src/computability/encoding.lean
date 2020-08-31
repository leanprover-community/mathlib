/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent.
-/

import data.fintype.basic
import data.num.lemmas
import tactic

/-!
# Encodings

This file contains the definition of a (finite) encoding, a map from a type to
strings in an alphabet, used in defining computability by Turing machines.
It also contains several examples:

## Examples

- `fin_encoding_nat_Γ₀₁`   : a binary encoding of ℕ in a simple alphabet.
- `fin_encoding_nat_Γ'`    : a binary encoding of ℕ in the alphabet used for TM's.
- `unary_fin_encoding_nat` : a unary encoding of ℕ
- `fin_encoding_bool_Γ₀₁`  : an encoding of bool.
-/

namespace computability

/-- An encoding of a type in a certain alphabet, together with a decoding. -/
structure encoding (α : Type) :=
(Γ : Type)
(encode : α → list Γ)
(decode : list Γ → option α)
(encodek : ∀ x, decode (encode x) = some x)

/-- An encoding plus a guarantue of finiteness of the alphabet. -/
structure fin_encoding (α : Type) extends encoding α :=
(Γ_fin : fintype Γ)

/-- An alphabet consisting of bit0 and bit1 -/
@[derive [inhabited,decidable_eq,fintype]]
inductive Γ₀₁
| bit0 | bit1

/-- A standard Turing machine alphabet, consisting of blank,bit0,bit1,bra,ket,comma. -/
@[derive [decidable_eq,fintype]]
inductive Γ'
| blank | bit0 | bit1 | bra | ket | comma

instance inhabited_Γ' : inhabited Γ' := ⟨Γ'.blank⟩

/-- The natural inclusion of Γ₀₁ in Γ'. -/
def inclusion_Γ₀₁_Γ' : Γ₀₁ → Γ'
| Γ₀₁.bit0 := Γ'.bit0
| Γ₀₁.bit1 := Γ'.bit1

/-- An arbitrary section of the natural inclusion of Γ₀₁ in Γ'. -/
def section_Γ'_Γ₀₁ : Γ' → Γ₀₁
| Γ'.bit0 := Γ₀₁.bit0
| Γ'.bit1 := Γ₀₁.bit1
| _ := arbitrary Γ₀₁

lemma left_inverse_section_inclusion : function.left_inverse section_Γ'_Γ₀₁ inclusion_Γ₀₁_Γ' :=
λ x, Γ₀₁.cases_on x rfl rfl

lemma inclusion_Γ₀₁_Γ'_injective : function.injective inclusion_Γ₀₁_Γ' :=
function.has_left_inverse.injective (Exists.intro section_Γ'_Γ₀₁ left_inverse_section_inclusion)

/-- An encoding function of the positive binary numbers in Γ₀₁. -/
def encode_pos_num : pos_num → list Γ₀₁
| pos_num.one := [Γ₀₁.bit1]
| (pos_num.bit0 n) := Γ₀₁.bit0 :: encode_pos_num n
| (pos_num.bit1 n) := Γ₀₁.bit1 :: encode_pos_num n

/-- An encoding function of the binary numbers in Γ₀₁. -/
def encode_num : num → list Γ₀₁
| num.zero := []
| (num.pos n) := encode_pos_num n

/-- An encoding function of ℕ in Γ₀₁. -/
def encode_nat (n : ℕ) : list Γ₀₁ := encode_num n

/-- A decoding function from `list Γ₀₁` to the positive binary numbers. -/
def decode_pos_num : list Γ₀₁ → pos_num
| (Γ₀₁.bit0 :: l) := (pos_num.bit0 (decode_pos_num l))
| (Γ₀₁.bit1 :: l) := ite (l = []) pos_num.one (pos_num.bit1 (decode_pos_num l))
| _ := pos_num.one

/-- A decoding function from `list Γ₀₁` to the binary numbers. -/
def decode_num : list Γ₀₁ → num := λ l, ite (l = []) num.zero $ decode_pos_num l

/-- A decoding function from `list Γ₀₁` to ℕ. -/
def decode_nat : list Γ₀₁ → nat := λ l, decode_num l

lemma encode_pos_num_nonempty (n : pos_num) : (encode_pos_num n) ≠ [] :=
pos_num.cases_on n (list.cons_ne_nil _ _) (λ m, list.cons_ne_nil _ _) (λ m, list.cons_ne_nil _ _)

lemma encodek_pos_num : ∀ n, (decode_pos_num(encode_pos_num n) ) = n :=
begin
  intros n,
  induction n with m hm m hm; unfold encode_pos_num decode_pos_num,
  { refl },
  { rw hm,
    exact if_neg (encode_pos_num_nonempty m) },
  { exact congr_arg pos_num.bit0 hm }
end

lemma encodek_num : ∀ n, (decode_num(encode_num n) ) = n :=
begin
  intros n,
  cases n; unfold encode_num decode_num,
  { refl },
  rw encodek_pos_num n,
  rw pos_num.cast_to_num,
  exact if_neg (encode_pos_num_nonempty n),
end

lemma encodek_nat : ∀ n, (decode_nat(encode_nat n) ) = n :=
begin
  intro n,
  conv_rhs {rw ← num.to_of_nat n},
  exact congr_arg coe (encodek_num ↑n),
end

/-- A binary encoding of ℕ in Γ₀₁. -/
def encoding_nat_Γ₀₁ : encoding ℕ :=
{ Γ := Γ₀₁,
  encode := encode_nat,
  decode := λ n, some (decode_nat n),
  encodek := λ n, congr_arg _ (encodek_nat n) }

/-- A binary fin_encoding of ℕ in Γ₀₁. -/
def fin_encoding_nat_Γ₀₁ : fin_encoding ℕ := ⟨encoding_nat_Γ₀₁, Γ₀₁.fintype⟩

/-- A binary encoding of ℕ in Γ'. -/
def encoding_nat_Γ' : encoding ℕ :=
{ Γ := Γ',
  encode := λ x, list.map inclusion_Γ₀₁_Γ' (encode_nat x),
  decode := λ x, option.some (decode_nat (list.map section_Γ'_Γ₀₁ x)),
  encodek := λ x, congr_arg _ $
    by rw [list.map_map, list.map_id' left_inverse_section_inclusion, encodek_nat] }

/-- A binary fin_encoding of ℕ in Γ'. -/
def fin_encoding_nat_Γ' : fin_encoding ℕ := ⟨encoding_nat_Γ', Γ'.fintype⟩

/-- A unary encoding function of ℕ in Γ₀₁. -/
def unary_encode_nat : nat → list Γ₀₁
| 0 := []
| (n+1) := Γ₀₁.bit1 :: (unary_encode_nat n)

/-- A unary decoding function from `list Γ₀₁` to ℕ. -/
def unary_decode_nat : list Γ₀₁ → nat := list.length

lemma unary_encodek_nat : ∀ n, unary_decode_nat (unary_encode_nat n) = n :=
λ n, nat.rec rfl (λ (m : ℕ) (hm : unary_decode_nat (unary_encode_nat m) = m), (congr_arg nat.succ hm.symm).symm) n

/-- A unary fin_encoding of ℕ. -/
def unary_fin_encoding_nat : fin_encoding ℕ :=
{ Γ := Γ₀₁,
  encode := unary_encode_nat,
  decode := λ n, some (unary_decode_nat n),
  encodek := λ n, congr_arg _ (unary_encodek_nat n),
  Γ_fin := Γ₀₁.fintype}

/-- An encoding function of bool in Γ₀₁. -/
def encode_bool : bool → list Γ₀₁
| ff := [Γ₀₁.bit0]
| tt := [Γ₀₁.bit1]

/-- A decoding function from `list Γ₀₁` to bool. -/
def decode_bool : list Γ₀₁ → bool
| [Γ₀₁.bit0] := ff
| [Γ₀₁.bit1] := tt
| _ := arbitrary bool

lemma encodek_bool : ∀ b, (decode_bool(encode_bool b)) = b := λ b, bool.cases_on b rfl rfl

/-- A fin_encoding of bool in Γ₀₁. -/
def fin_encoding_bool_Γ₀₁ : fin_encoding bool :=
{ Γ := Γ₀₁,
  encode := encode_bool,
  decode := λ x, some(decode_bool x),
  encodek := λ x, congr_arg _ (encodek_bool x),
  Γ_fin := Γ₀₁.fintype }

instance inhabited_fin_encoding : inhabited (fin_encoding bool) := ⟨fin_encoding_bool_Γ₀₁⟩

instance inhabited_encoding : inhabited (encoding bool) := ⟨fin_encoding_bool_Γ₀₁.to_encoding⟩

end computability
