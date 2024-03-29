# Model Files

| File       | Description     |
|------------|-----------------|
| `manual.smv` | Initial model. Written by hand. Meets all specifications |
| `generated.smv` | Model generated by model_gen.py with NUM_BITS = 5 and NUM_NODES = 3. Extremely long runtime. Have not seen it complete. |
| `modified.smv` | Same model has `generated.smv`. The finger tables and associated transitions have been modified by hand. This is able to complete. Meets all specifications. |

## Model Verification

```commandline
$ nuXmv manual.smv
```

# Model Generator

## Execution
Use the following command to run the model generator:
```commandline
$ python3 model_gen.py > generated.smv
```

## Configuration

| Variable | Meaning |
|----------|---------|
|` NUM_BITS` | The number of bits allowed in a node id as well as the number of rows in the finger table |
| `NUM_NODES` | The number of nodes in the cluster. Must be less than `2^NUM_BITS - 1` |

# Report

[`CS 6315 Automated Verification Final Project.pdf`](https://github.com/kstudzin/CS6315/files/9543657/CS.6315.Automated.Verification.Final.Project.pdf)
