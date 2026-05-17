# hlf-baseToken-model

## Description

This repository contains a TLA+ model and configuration file for model checking (with Apalache BMC) the HyperLedger Fabric BaseToken logic. The model follows the logic of the token implementation and focuses on core operations (transfers, buy/buyback, emission, rates, limits, fees). The reference implementation: https://github.com/anoideaopen/foundation/tree/main/token

## Installation and Run

### Apalache installation

Follow the Apalache installation guide: https://apalache-mc.org/docs/apalache/installation/index.html

### Run

Bounded Model Checking:

```sh
apalache-mc check --config=BaseTokenApalache.cfg --length=5 --discard-disabled BaseToken.tla
```

Simulation mode:

```sh
apalache-mc simulate --config=BaseTokenApalache.cfg --length=12 --max-run=100 --discard-disabled BaseToken.tla
```

## Publications

Article (in Russian): https://habr.com/p/993688/
