# Proof Caching

See also the [end-user documentation](../../user/ProofCaching/).

## On-disk database

### Proofs

When adding a proof to the database, the following is done:

- a copy is saved in ~/.key/cachedProofs/
- the Java source file(s) are saved
- included `.key` files are saved
- metadata is updated (see below)

### Java source files, .key files

When these are referenced in a proof, they will be copied into `~/.key/cachedProofs/` using a simple content-addressing scheme.

The proof header is modified to refer to a new `~/.key/cachedProofs/javaSource123456` directory containing hardlinked copies of the source files.

### Metadata

Filename: `~/.key/cachedProofs.json`.

Planned format: JSON.

Schema: ([schema playground](https://dashjoin.github.io/#/schema))
```
{
  "type": "object",
  "properties": {
    "proofs": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "name": {
            "type": "string"
          },
          "file": {
            "type": "string"
          },
          "keyVersion": {
            "type": "string"
          },
          "choiceSettings": {
            "type": "string"
          },
          "referencedFiles": {
            "type": "array",
            "items": {
              "type": "string"
            }
          },
          "cachedSequents": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "stepIndex": {
                  "type": "number"
                },
                "sequent": {
                  "type": "string"
                }
              }
            }
          },
          "cachedGraph": {
            "type": "object",
            "properties": {
              "nodes": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "edges": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "in": {
                      "type": "array",
                      "items": {
                        "type": "string"
                      }
                    },
                    "out": {
                      "type": "array",
                      "items": {
                        "type": "string"
                      }
                    }
                  }
                }
              }
            }
          },
          "classpathHash": {
            "type": "string"
          },
          "bootclasspathHash": {
            "type": "string"
          }
        }
      }
    },
    "files": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "file": {
            "type": "string"
          },
          "hash": {
            "type": "string"
          }
        }
      }
    }
  }
}
```

proof.choiceSettings should encode taclet options and other relevant properties (e.g. OSS use).

proof.classpathHash should encode the entire classpath if it is explicitly set. Otherwise it should identify the classpath provided by the used KeY version.

proof.keyVersion should help filter out proofs that are unlikely to load.

Example:
```
{
  "proofs": [
    {
      "name": "sumAndMax",
      "file": "proof12345.proof",
      "keyVersion": "2.13.0",
      "choiceSettings": "xxxx",
      "referencedFiles": [
        "java123456.java"
      ],
      "cachedSequents": [
        {
          "stepIndex": 15,
          "sequent": "a==>b"
        }
      ],
      "cachedGraph": {
        "nodes": [
          "false ==>",
          "Closed goal 1"
        ],
        "edges": [
          {
            "in": [
              "false ==>"
            ],
            "out": [
              "Closed goal 1"
            ]
          }
        ]
      },
      "classpathHash": null,
      "bootclasspathHash": null
    }
  ],
  "files": [
    {
      "file": "java123456.java",
      "hash": "41847972b9c92994502c60c58b406f098ef0afae"
    }
  ]
}
```