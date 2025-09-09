# CL Playground

用于测试二次型的判别式 $$\Delta_K=-pq$$ 是否安全. 原理是测试生成元 $$g$$ 的小质数幂是否为零元.

以下命令用于跑完整个质数表的第 `m/n` 部分.

```
cargo run --release --bin play -- m/n
```

运行时间较长. 建议放在tmux里运行.

## 如果运行中止, 提示以下字样, 请务必及时联系作者 !

```
⟨g⟩ has small prime subgroup of order: ...
```
