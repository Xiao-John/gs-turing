# GS-Turing · 私有研究基线

这是 Gray–Scott 计算嵌入研究的**精选版本基线**，不是 Mac 上多 agent 工作区的镜像，也不是公开发布。当前没有 Gray–Scott 通用计算证明，或通过完整验收的真实级联。Lean 库中的边界定理、网格证书和理想模型结果不等于物理装置验证。

- `core/` 和 `numerics/`：求解器与数值工具。
- `configs/`：实验参数；除下述 smoke 外，其余配置可能需要未纳入的原始实验输入或专用脚本。
- `experiment/` 和 `verify/`：通用复现入口、示例及求解器交叉检查。
- `GS_Theorem_lib/`：Lean 4.36 的源码、冻结证书与构建审计脚本。库内提到的部分研究笔记位于原工作区，不随此快照迁移。
- `SOURCE_MANIFEST.sha256`：所导入的文件与哈希，可用 `shasum -a 256 -c SOURCE_MANIFEST.sha256` 验证。

## 轻量核对

在已安装 `requirements.txt` 中依赖的 Python 环境中运行：

```sh
python -m verify.check_solvers --n 64 --steps 30
python -m experiment.runner configs/smoke.json --dry
```

完整 Lean 构建用 `cd GS_Theorem_lib && ./scripts/audit.sh`；计算较重时使用批准的计算环境。大规模结果留在原存储，后续有需要时只登记相对路径、运行版本和校验值，不提交原始数据或计算凭据。

## 同步约定

原工作区仍是 agent 实时协作地，NOW 和会话不入此仓。后续将经复核的源码、配置、小型证据和重要决策摘要补到此仓的独立克隆，再用提交或 PR 管理；不要把原工作区整棵目录或旧历史推上来。维持私有，未在此授予新的开源许可。
