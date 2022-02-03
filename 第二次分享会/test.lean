import data.rat.basic
       data.nat.parity
       tactic

--sqrt(2) is irrational

lemma even_if_square_even {n : ℕ} (hn2 : 2 ∣ (n*n)) : 2 ∣ n :=
begin
  by_contra hc,
  have hmod2 : n % 2 = 1, from nat.not_even_iff.mp hc,
  set k := n / 2 with hk,
  have hn : n = 1 + 2*k,
  { rw [←nat.mod_add_div n 2, hmod2] },
  have hnn : n*n = 1 + 2*(2*k + 2*k*k),
  { rw hn, ring },
  rw [nat.dvd_iff_mod_eq_zero, hnn] at hn2,
  norm_num at hn2,
end

--¬ : Prop → false

theorem sqrt_2_irrational : ¬∃ (p : ℚ), p^2 = 2 :=
begin
  by_contra h,
  cases h with p hp,
  set m := int.nat_abs p.num with hm,
  set n := p.denom with hn,
  have hm2 : p.num * p.num = m * m,
  { norm_cast,
    rw [hm, int.nat_abs_mul_self] },
  have hcop := p.cop,
  rw [←hm, ←hn] at hcop,
  rw [pow_two, rat.eq_iff_mul_eq_mul, rat.mul_self_num, rat.mul_self_denom, hm2, ←hn] at hp,
  norm_cast at hp,
  rw mul_one at hp,
  have hmmeven : 2 ∣ m * m,
  { rw hp,
    exact nat.dvd_mul_right _ _ },
  have hmeven : 2 ∣ m, from even_if_square_even hmmeven,
  have hmeven := hmeven,
  cases hmeven with k hk,
  rw [hk, mul_mul_mul_comm, mul_assoc, nat.mul_right_inj (show 0 < 2, by norm_num)] at hp,
  have hnneven : 2 ∣ n * n,
  { rw ←hp,
    exact nat.dvd_mul_right _ _ },
  have hneven : 2 ∣ n, from even_if_square_even hnneven,
  refine nat.not_coprime_of_dvd_of_dvd (by norm_num) hmeven hneven hcop,
end
