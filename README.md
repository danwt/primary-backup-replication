# primary-backup-replication

TLA+ for [primary backup replication](https://danwt.github.io/190406129916449788032140476169340981634).

```bash
# Check
java -XX:+UseParallelGC -Xmx12g -cp tla2tools.jar tlc2.TLC -workers auto spec.tla
# Typecheck
java -XX:+UseParallelGC -Xmx12g -jar apalache-pkg-0.20.3-full.jar typecheck spec.tla
```

This TLA+ model is of one-shot primary backup replication. That is, a client writes a value to a replicated register once. The multi-shot algorithm simply calls the one-shot algorithm, and isn't interesting to model.

The failure model is crash-stop.
