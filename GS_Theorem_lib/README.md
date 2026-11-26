# GS_Theorem_lib

Gray–Scott / Enhanced Gray–Scott（EGS）项目的**纯 Lean 4.36.0 迷你定理库**。

- **零外部依赖**：仅依赖 Lean `v4.36.0` 核心库 `Init` 与原生精确有理数 `Rat`，不依赖 Mathlib。
- **严格内核审计**：全库零 `sorry`、零 `admit`、零自定义 `axiom`、零 `native_decide`（无 `Lean.ofReduceBool` 编译器信任公理）；所有定理仅依赖 Lean 标准公理 `[propext, Classical.choice, Quot.sound]`（其中 `pi_machin_enclosure` 零公理）。

## 快速构建与一键审计

```bash
cd GS_Theorem_lib
./scripts/audit.sh
```

`audit.sh` 依次执行：
1. 静态扫描全部 `.lean` 源码，确认零 `sorry`/`admit`/`axiom`/`native_decide`；
2. 全量 `lake build`（32 jobs，含全部 4 套终审命题与 `M-44` 2,269 段内核 `decide` 证书）；
3. 对核心层与全部 4 套终审主定理执行 `#print axioms` 审计。

## 目录结构

| 模块 | 作用 |
|---|---|
| `GSTheoremLib.lean` | 全库总入口（一键编译全部核心与定理模块） |
| `GSTheoremLib/Core/QPair.lean` | 纯整数对 `QPair := Int × Nat` 精确算术（内核 `decide` 快速规约）及到 `Rat` 的完整保序/保算术桥接 |
| `GSTheoremLib/Core/Nagumo.lean` | 双稳 Nagumo 反应 `nagumoUnit` / `nagumoScaled` / 势能 `nagumoPotential`、SOS 单侧 Lipschitz 常数 `79/300`、尾区负性与零微积分区间上界 `fMaxUB` |
| `GSTheoremLib/Core/Enclosure.lean` | Machin $\pi$ 零公理包络、`exp(±1/50)` 12 位外扩步进表与 `Exp50Spec` 通用接口 |
| `GSTheoremLib/Theorems/PlanarCrossover.lean` | 平面单调电路双轨取反障碍（含 `InputPortUnique` 单端口模型）与 3 个严格平面零交叉器件（XOR / SWAP / INHIBIT→NAND） |
| `GSTheoremLib/Theorems/M23Supersolution.lean` | `M-23` 原生 `Rat` 显式 Euler 离散单调性、全时超解比较原理、`h/2` 5pt/9pt 精确实例化与耦合模板继承 |
| `GSTheoremLib/Theorems/M27SymmetryContraction.lean` | `M-27` 双稳 Nagumo 对称直通道全局割线斜率界、临界自对中宽度 $W_{\mathrm{sym}} \in (39.151462, 39.151463)$ 格、全时离散空间屏障归纳、反对称 $\ell^2/\ell^\infty$ 精确不等式与四组（`h_0/h/2` × `5pt/9pt`）出口收缩证书 |
| `GSTheoremLib/Theorems/M41ScalarReset.lean` | `M-41` 离散 Ginzburg–Landau Lyapunov 能量下降、负能量复位障碍、四组网格精确常数与阈值见证一致燃料耗尽 |
| `GSTheoremLib/Theorems/M44/` | `M-44` 连续 T 域钉扎界（`ContinuumPinning`）、纯整数内核核验器（`CertCheck`）、全部 4 份冻结 JSON 2,269 段内核验证（`CertW15..W18`）、完备性桥接（`SoundBridge`）与端到端实例化（`EndToEnd`） |
| `scripts/audit.sh` | 一键全库构建 + 禁词扫描 + `#print axioms` 审计脚本 |

## 命题状态与外部边界说明

以下 **PlanarCrossover、M-23、M-41、M-44** 对应已有终审；**M-27 是未终审的探索性理想直颈原型**，仅列入下表以便追溯，其 Lean 可编译不构成项目终审或真实装置验证。

| 命题 | 对应终审 | Lean 内核已证核心结果 | 仍位于无 Mathlib Lean 之外的外部桥接 |
|---|---|---|---|
| **PlanarCrossover** | `coordination/confirm/2026-11-21_planar_nonmonotone_crossover/VERDICT.md` | 单调电路不可单轨取反；固定端口/单端口双轨取反在闭圆盘平面嵌入下不可行；3 器件严格平面性与真值表 | 闭圆盘 Jordan 拓扑交叉障碍（由假设项显式接入）；完整连续 PDE 物理实现 |
| **M-23** | `coordination/confirm/2026-11-22_m23_h2_rational_supersolution/VERDICT.md` | 任意分母 `Rat` 轨迹单调性、全时超解比较与阈值下钉扎；`h/2` 5pt/9pt 精确参数构造与耦合模板继承 | 34,560 格真实掩膜数组向 Lean 的逐格绑定；全耦合 GS/P2 感知前提 |
| **M-27** (`[EXPLORE]`) | `sandbox/2026-11-23_agent3_m27_symmetry_contraction_theorem/NOTE.md` | 全局割线斜率界 `[-7/2000, 79/60000]` 与偶对称性；$W_{\mathrm{sym}} \in (39.151462, 39.151463)$ 格及 $w\le 39$ 正阻尼/$w=40$ 越界；封闭 Neumann 末端全时离散空间屏障归纳；反对称向量 $\|v\|_2^2\le w/4$ 与 $(a_i-a_{\mathrm{rev}})^2\le 2\|v\|_2^2$；`h_0`(`w=25,L=107`) `5pt < 2.537e-4` / `9pt < 2.503e-4` 与 `h/2`(`w=50,L=214`) `5pt < 3.379e-4` / `9pt < 3.368e-4` 精确证书 | 连续 Wirtinger–Poincaré 与 1D 抛物比较原理；二维离散矩阵到行 $\ell^2$ 递推的谱范数桥接（含交错级数 $\sin$ 余项）；仅限孤立对称直颈+封闭 Neumann 末端，不直接推广至真实弯道/发射腔或全耦合 GS 输出映射 |
| **M-41** | `coordination/confirm/2026-11-23_m41_scalar_reset/VERDICT.md` | 离散 Ginzburg–Landau 能量严格下降；负能量不可复位；四组网格精确常数；阈值见证推一致燃料耗尽 | 连续 PDE 分部积分；6,757 格 × ~83k 步整数下解见证执行；浮点舍入桥接 |
| **M-44** | `coordination/confirm/2026-11-23_m44_continuum_pinning/VERDICT.md` | `K=79/300` SOS、Machin $\pi$、$s(0,0)>-0.42$、全部 4 份冻结 JSON（2,269 段）内核 `decide` 验证及 `checkFullRawCert → Rat` 端到端逐点 PDE 超解与全局上界（`w=15/16` 全 $s\ge -0.42 < 3/5$；`w=17/18` 全 $s\ge 0 < 3/5$） | Schwarz–Christoffel 连续复分析双全纯性；实分析级数余项桥接；重入角 $H^1$ 与无界域加权 $L^2$ Gronwall 弱比较 |

## 后续扩展规范

新增已终审命题时：
1. 优先复用 `GSTheoremLib/Core/{QPair, Nagumo, Enclosure}`，避免重复证明基础引理；
2. 在 `GSTheoremLib/Theorems/` 下新增对应模块并在 `GSTheoremLib.lean` 中导入；
3. 将新模块的主定理加入 `scripts/audit.sh` 并跑通 `./scripts/audit.sh`（零报错、零警告、零 `sorry`/自定义公理）后再登记至 `coordination/NOW.md`。
