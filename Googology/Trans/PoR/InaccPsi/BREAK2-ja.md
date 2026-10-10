[← Back](README-ja.md) | [English](BREAK2.md) | [Japanese](BREAK2-ja.md)

# $`R_2^+`$ の骨組みが終わるところ（続き）：$`\nu_C`$ と $`R_2^C`$ の核についてのあとの評価

このページは [BREAK-ja.md](BREAK-ja.md) の続き。[BREAK-ja.md](BREAK-ja.md) §2 の定理 NU-CT の系に付いていた、あとの評価の一覧をここに移した。そのページの数式が GitHub の表示できる
量に収まるようにするため。状態の言葉は [README-ja.md](README-ja.md) §3 のもの。どの行も、引いたページでの査読の回数を持つ。

## 1. NU-CT の系のあとの評価

[BREAK-ja.md](BREAK-ja.md) §2 は $`\beta_0 \ge \nu_C \gt \nu_P`$ と $`[0, \nu_C] \subseteq \mathrm{Core}(R_2^C)`$ を証明する（$`R_2^C`$。査読 1 回）。あとの回がこの順に評価を上げた。「FRAG のもと」は引いたページと同じ。

| 評価 | 仮定 | 場所 |
|---|---|---|
| $`\nu_C \gt \upsilon^* = \psi_{\Omega_1}(\Omega_\omega + \Omega_2)`$（査読 1 回）、そして $`\nu_P \ge \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$（移し） | 無し | [THETA-ja.md](THETA-ja.md) §1 |
| $`\nu_P = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+2})`$、$`\nu_C \ge \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{\theta+3}\cdot 2)`$ | 無し | [THETA-ja.md](THETA-ja.md) §9.1 |
| $`\nu_C \ge X_4 = \psi_{\Omega_1}(\Omega_\omega + \omega^{\theta_2+2} + \omega^{G_2+1}\cdot 2)`$、$`G_2 = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+2})`$ | 無し | [SHIFT-ja.md](SHIFT-ja.md) §1 |
| $`\nu_C \ge X_5`$。$`\nu_C \ge X_8`$ | FRAG | [SHIFT-ja.md](SHIFT-ja.md) §8.1。§9.1 |
| $`\nu_C \ge X_9`$。$`X_{11}`$。$`X_{12}`$ | FRAG | [SHIFT2-ja.md](SHIFT2-ja.md) §1.1。§2.1。§3.1 |
| $`\nu_C \ge X_{13}`$。$`X_{14}`$ | FRAG | [SHIFT3-ja.md](SHIFT3-ja.md) §1.1。§2.1 |
| $`\nu_C \ge X_{15}`$。$`X_{16}`$。$`X_{17}`$ と $`X_{18}`$ | FRAG | [SHIFT4-ja.md](SHIFT4-ja.md) §1.1。§1.4。§2.1、§2.2 |
| $`\nu_C \ge X_{19}`$。$`X_{21}`$ | FRAG | [SHIFT5-ja.md](SHIFT5-ja.md) §1.1。§2.1 |
| $`\nu_C \ge X_{22}`$ と $`X_{23}`$ | FRAG | [SHIFT6-ja.md](SHIFT6-ja.md) §1.1、§2.1 と、§3.1 の直し |
| $`\nu_C \ge L(\omega+1) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P')`$ | FRAG | [SHIFT7-ja.md](SHIFT7-ja.md) §1.1 |
| $`\nu_C = \nu_S = L(\omega+1)`$（監査済み） | FRAG | [SHIFT7-ja.md](SHIFT7-ja.md) §2.1、§3.1 |
| $`\nu_C`$ の上で $`[0, y^C_\nu] \subseteq \mathrm{Core}(R_2^C)`$、$`y^C_\nu \ge X_A = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+1} + P' + \omega^{\theta+3}\cdot 2)`$ | FRAG | [SHIFT7-ja.md](SHIFT7-ja.md) §3.2 |
| $`[0, L(\Omega_1\cdot\omega)] \subseteq \mathrm{Core}(R_2^C)`$ | FRAG | [SHIFT8-ja.md](SHIFT8-ja.md) §1.1 |
| $`[0, L(\varepsilon_{\Phi_\Omega+1})] \subseteq \mathrm{Core}(R_2^C)`$ | FRAG | [SHIFT8-ja.md](SHIFT8-ja.md) §2.1 |
| $`[0, L(G_2)] \subseteq \mathrm{Core}(R_2^C)`$、$`L(G_2) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{P'+G_2})`$（$`L(\varepsilon_{\Phi_\Omega+1}+\omega^2)`$ までは 2 つの証明で査読 2 回） | FRAG | [SHIFT9-ja.md](SHIFT9-ja.md) §1.1、§1.2 |
| $`[0, L(\Omega_2+\Phi^{P'}\cdot\omega)] \subseteq \mathrm{Core}(R_2^C)`$、$`L(\Omega_2+\Phi^{P'}\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \Omega_2 + \omega^{\Phi^{P'}+1})`$（$`L(G(\Omega_1)\cdot\omega)`$ までは 2 つの証明で査読 2 回） | FRAG | [SHIFT9-ja.md](SHIFT9-ja.md) §2.1、§2.2 |
| $`[0, L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega)] \subseteq \mathrm{Core}(R_2^C)`$、$`L(\theta'_2\cdot(\omega+1)+G''(\omega+1)\cdot\omega) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+1} + \theta'_2 + \omega^{G''(\omega+1)+1})`$（$`Z^\Gamma = L(\Omega_2\cdot(\omega+1)+\Phi^{P'}_{\omega+1}\cdot\omega+\omega^2)`$ までは 2 つの証明で査読 2 回） | FRAG | [SHIFT9-ja.md](SHIFT9-ja.md) §3.1、§3.2 |
| $`[0, Z^{\mathrm{LL}}] \subseteq \mathrm{Core}(R_2^C)`$、$`Z^{\mathrm{LL}} = L(\theta'_2\cdot\omega^2+\omega^{G''(\omega^2)^2}) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + \omega^{\theta'_2+2} + \omega^{\omega^{G''(\omega^2)\cdot 2}})`$（$`Z^\varepsilon`$ までは 2 つの証明で査読 2 回） | FRAG | [SHIFT10-ja.md](SHIFT10-ja.md) §1.1、§1.2 |

ここで $`L(e) = \psi_{\Omega_1}(\Omega_\omega\cdot 2 + P'\cdot e)`$、$`P' = \psi_{\Omega_2}(\Omega_\omega\cdot 2)`$、$`\Phi_\Omega = \psi_{\Omega_2}(\Omega_2)`$、$`\theta = \psi_{\Omega_2}(\Omega_\omega)`$、$`\theta_2 = \psi_{\Omega_3}(\Omega_\omega)`$、$`\Phi^{P'} = \psi_{\Omega_2}(\Omega_\omega\cdot 2+\Omega_2)`$、$`G(\Omega_1) = \psi_{\Omega_2}(\Omega_\omega + \omega^{\theta_2+\Omega_1})`$、$`\theta'_2 = \psi_{\Omega_3}(\Omega_\omega\cdot 2)`$、$`G''(\zeta) = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \theta'_2\cdot\zeta)`$、$`\Phi^{P'}_\zeta = \psi_{\Omega_2}(\Omega_\omega\cdot 2 + \Omega_2\cdot\zeta)`$。$`Z^\varepsilon`$ は [SHIFT10-ja.md](SHIFT10-ja.md) §1 で定める。点 $`X_n`$ の名前は
[README-ja.md](README-ja.md) §2 と引いたページにある。
