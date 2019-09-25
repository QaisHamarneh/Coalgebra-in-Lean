import category_theory.category
import category_theory.types

import tactic.tidy


namespace help_functions

universe u


open classical function set

variables {A B C : Type u}

lemma eq_in_set {A : Type u} {S: set A} {a b: S}
: a.val = b.val ↔ a = b := 
    by {cases a, cases b, dsimp at *, simp at *}

@[simp , tidy] def inclusion (S : set A) 
    : S → A := λ s , s 
notation S ` ↪ ` A := @inclusion A S

@[simp , tidy] lemma  inclusion_id
     (A : Type u) (S : set A) (s : S)
    : (inclusion S) s = s := by simp 

@[simp , tidy] lemma inj_inclusion (A : Type u) (S : set A) 
        : injective (inclusion S) := by tidy

@[simp , tidy] lemma comp_inclusion (A : Type u) (S T: set A) (h: S ⊆ T)
    : (S ↪ A) = (T ↪ A) ∘ (set.inclusion h)
        := by tidy
 

noncomputable def graph_to_map 
                 (G :  A → B → Prop)
                 (h : ∀ a : A , ∃! b : B, G a b) : A → B :=
                 λ a , some (h a)



def map_to_graph (f : A → B): set (A × B ):= λ r, r.2 = f r.1 


lemma bij_map_to_graph_fst (f : A → B) :
    let π₁ : (map_to_graph f) → A := λ r , r.val.1 in 
    bijective π₁ := 
    begin
        let R : set (A × B) := map_to_graph f,
        let π₁ : R → A := λ r , r.val.1, 
        have inj : injective π₁ := 
            begin
                assume a₁ a₂ (πa₁_πa₂ : a₁.val.1 = a₂.val.1),
                have a1_p : a₁.val.2 = f a₁.val.1 := a₁.property,
                have a2_p : a₂.val.2 = f a₂.val.1 := a₂.property,
                have a_a : f a₁.val.1 = f a₂.val.1 := by tidy,
                have a2_p : a₁.val.2 = a₂.val.2 := by simp [a1_p, a2_p, a_a],
                tidy
            end,
        have sur : surjective π₁ := 
            begin
                intro a,
                let r := (⟨a , f a⟩ : A × B),
                have r_R : r ∈ R := 
                    have r2_fr1 : r.2 = f r.1 := by simp,
                    r2_fr1,
                use r,
                tidy
            end,
        exact ⟨inj, sur⟩
    end

noncomputable def invrs (f : A ⟶ B) (bij : bijective f) : B ⟶ A :=
                some (iff.elim_left bijective_iff_has_inverse bij)

lemma invrs_id (f : A ⟶ B) (bij : bijective f) 
    : 
    f ∘ (invrs f bij) = id := 
        begin
            have h0 : left_inverse (some _) f ∧ right_inverse (some _) f := 
                some_spec (iff.elim_left bijective_iff_has_inverse bij),
            have h1: right_inverse _ f := 
                        and.elim_right h0,
            by tidy
        end

lemma id_invrs (f : A ⟶ B) (bij : bijective f) :
    (invrs f bij) ∘ f = id := 
    begin
        have h0 : left_inverse (some _) f ∧ right_inverse (some _) f := 
            some_spec (iff.elim_left bijective_iff_has_inverse bij),
        have h1: left_inverse _ f := 
                    and.elim_left h0,
        by tidy
    end




def kern (f : A ⟶ B) : A → A → Prop := 
        λ a₁ a₂ , f a₁ = f a₂

def sub_kern (f : A ⟶ B) (g : A → C) : Prop :=
    ∀ a₁ a₂, kern f a₁ a₂ → kern g a₁ a₂

@[simp, tidy] def kern_comp (f : A ⟶ B) (g : B → C) :
        sub_kern f (g ∘ f) := 
    assume a b k_f, 
    have f_ab : f a = f b := k_f,
    show g (f a) = g (f b), from by rw [f_ab]






def emptyOrNot (S : set A) : (nonempty S) ∨ ¬ (nonempty S)  
        := em (nonempty S)


noncomputable def nonemptyInhabited {S : set A} (h : nonempty S)
        : inhabited S 
        := inhabited.mk (choice h)



lemma map_from_empty (S : set A) (B : Type u) : 
            (¬ ∃ s : S , true) → 
            ∀ f₁ f₂  : S → B, f₁ = f₂ := 
            assume h f₁ f₂,
            show f₁ = f₂, from 
            have h0 : ∀ s : S , false := by tidy,
            by tidy


lemma nonempty_notexists {S : set A}: 
        ¬ nonempty S → (¬ ∃ s : S , true) :=
        assume nonemp ext,
            show false,
            from nonemp (nonempty_of_exists ext)



lemma only_one {p q: A → Prop} 
                (ex_uni : ∃! a , p a)
                (ex : ∃ a , p a ∧ q a)
        : ∃! a , p a ∧ q a := 
        let a : A := some ex_uni in
        have h : _ := some_spec ex_uni,
        have h1 : ∀ a₁ , p a₁ → a₁ = a :=
                and.right h,
        let a₁ : A := some ex in
        have h2 : p a₁ ∧ q a₁ := some_spec ex,
        have h3 : a₁ = a := h1 a₁ (and.left h2), 
        have h4 : ∀ a₂ , p a₂ ∧ q a₂ → a₂ = a₁ := 
            λ a₂ pq, by rw [h3, (h1 a₂ (and.left pq))],
        exists.intro a₁ ⟨ h2 , h4⟩  


lemma eq_range_if_surjective  (f: A ⟶ B) (g: B ⟶ C)
    (sur: surjective f) : range g = range (g ∘ f):= 
    calc range g = image g (univ)         : by simp
          ...    = image g (range f)      : by rw [range_iff_surjective.2 sur]
          ...    = range (g ∘ f)          : by tidy


lemma sub_kern_if_injective {X Y Z U : Type u}
    (e : X ⟶ Y) (f : Y ⟶ U)
    (g : X ⟶ Z) (m : Z ⟶ U)
    (h : e ≫ f = g ≫ m) (inj: injective m) : sub_kern e g := 
        begin
            assume x₁ x₂ xxe,
            have h01 : e x₁ = e x₂ := xxe,
            have h02 : m (g x₁) = m (g x₂) := 
            calc m (g x₁) = (g ≫ m) x₁    : rfl
                   ...    = (e ≫ f) x₁    : by rw h
                   ...    = f (e x₁)       : rfl
                   ...    = f (e x₂)       : by rw h01
                   ...    = (e ≫ f) x₂    : rfl
                   ...    = (g ≫ m) x₂    : by rw h,
            exact inj h02
        end


lemma eq_sets {A : Type u} {S T : set A}
    : (∀a : A ,a ∈ S ↔ a ∈ T) ↔  S = T  := 
    begin 
        split,
        assume h,
        have h1 : ∀s : S , s.val ∈ T :=
           λ s, (h s.val).1 s.property,
        have h2 : ∀t : T , t.val ∈ S :=
           λ t, (h t.val).2 t.property, 
        simp at *,  
        ext1 x, 
        split, 
        intros s, 
        exact h1 x s, 
        intros t, 
        exact h2 x t,
        intro h,
        intro a, 
        induction h, 
        refl
    end

@[tidy] def fun_of_two_eq_sets {A B: Type u} {S T : set A}
    (h: ∀a : A ,a ∈ S ↔ a ∈ T)
    (f: S → B):
    T → B := 
        λ t , 
        f ⟨t.val , (h t.val).2 t.property⟩


@[tidy] lemma eq_fun_of_eq_sets {A B: Type u} (S T : set A) 
    (h: ∀a : A ,a ∈ S ↔ a ∈ T)
    (f: S → B):
    let fT : T → B := (fun_of_two_eq_sets h f) in
    ∀ s , f s = fT ⟨ s.val , (h s.val).1 s.property⟩ 
    := by tidy



@[tidy] lemma def_of_range {A B: Type u} (T: set A)
        (f: T → B) (b : B) :
    (∃ (a : A) (h : a ∈ T), f ⟨a, h⟩ = b) ↔
    b ∈ range f := by tidy  


@[tidy] lemma eq_ranges {A B: Type u} {S T : set A} 
    (h: ∀a : A ,a ∈ S ↔ a ∈ T)
    (f: S → B):
    let fT : T → B := (fun_of_two_eq_sets h f) in
    range f = range fT
    := 
    begin
        intro fT,
        have h1 : ∀b : B ,b ∈ range f ↔ b ∈ range fT :=
            begin 
                intro b,
                split,
                intro bf,
                let s := some bf,
                have spec : f s = b := some_spec bf,
                have eq : fT ⟨ s.val , (h s.val).1 s.property⟩ = f s := 
                    eq.symm (eq_fun_of_eq_sets S T h f s),

                have ex : ∃ t : T , fT t = b := 
                    exists.intro 
                    (⟨ s.val , (h s.val).1 s.property⟩ : T) 
                    (by rw [eq , spec]),
                exact ex,
                intro bfT,
                tidy
            end,
        exact eq_sets.1 h1 
    end

def img_comp {X Y Z : Type u} (f : X → Y) (g : Y → Z) (s : set X):
    image g (image f s) = image (g ∘ f) s := 
    begin
        have h3: ∀ z : Z, (z ∈ image g (image f s)) ↔  
                    (z ∈ image (g ∘ f) s)
                    := 
            begin
                intro z,
                split,
                intro el,
                cases el with fa specFA,
                cases specFA.1 with a specA,
                use a,
                split,
                exact specA.1,
                simp [specA.2 , specFA.2],
                intro ex,
                cases ex with a spec,
                have fa_Y : f a ∈ image f s := 
                    begin use a, tidy end,
                have gfa_Z : g (f a) ∈ image g (image f s) :=
                    begin 
                        use f a,
                        split,
                        simp,
                        tidy

                    end,
                rw ← spec.2,
                exact gfa_Z
            end,
        exact eq_sets.1 h3

    end




lemma not_and_left {p q : Prop}: ¬ (p ∧ q) → p → ¬ q :=
    λ hnpq , λ hp , λ hq, absurd (and.intro hp hq) hnpq

lemma not_and_right {p q : Prop}: ¬ (p ∧ q) → q → ¬ p :=
    λ hnpq , λ hp , by {intros a, simp at *, solve_by_elim}


end help_functions



def if_func (p : Prop) [decidable p] : Prop := 
        if p
            then p
            else ¬p

lemma solving_if_func (p : Prop) [d : decidable p] : if_func p :=
    match d with
    | is_true h := h
    | is_false nh := nh
    end
    
def fun_using_if_fun (p : Prop) [decidable p] : ℕ := 
    let some_fun : Prop :=         -- same thing with let ... in
                if p
                    then p
                    else ¬p in
    have some_proof : some_fun := 
        begin
            dsimp [some_fun], -- some_fun, 
            split_ifs, 
            exact h,
            exact h
        end,
    1

def fun_using_if_fun_tactic (p : Prop) [decidable p] : ℕ :=
    begin
        let some_fun : Prop :=         -- same thing with let ... in
                    if p
                        then p
                        else ¬p,
        have some_proof : some_fun := 
            begin
                dsimp [some_fun],
                split_ifs, 
                exact h,
                exact h
            end,
        exact 1
    end


def eff_len {A : Type*} [inhabited A] (n : ℕ) : 
        list A          →   ℕ
        | []           :=  n
        | (h::tl)      :=  (eff_len tl)

def subsubset {A: Type*} {V : set A} {U : set V} : set A
    :=  subtype.val '' U      -- or just u.val



