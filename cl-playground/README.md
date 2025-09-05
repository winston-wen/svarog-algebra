# CL Playground

用于测试二次型的判别式 $$\Delta_K=-pq$$ 是否安全. 原理是测试生成元 $$g$$ 的小质数幂是否为零元.

用法

```
cargo run --release -- -f 200000 -t 400000
```

运行时间较长. 建议放在tmux里运行.

## 如果运行中止, 提示以下字样, 请务必及时联系作者 !

```
⟨g⟩ has small prime subgroup of order: ...
```
