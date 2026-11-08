# Spikes

Small, self-contained proofs of concept that settle the SHAPE of a design before it moves into the
compiler and its proof (`formal/`). A spike is cheap to change: it imports nothing outside `Spikes/` but
the standard library, it checks in seconds, and no gate or backstop reads it. Once its shape is settled,
the design is recorded as a D-entry and migrated into `formal/`; the spike then stays only as long as its
plan is open.

Each spike directory names its plan:

| directory | plan | what it shapes |
|---|---|---|
| `LinCore/` | 0.146 (memory by a linear core) | the linear core Once compiles through: its terms, its alloc/free events over D402's two heaps, `NoLeak` and the space claim, then the pass from `Once.IR` |

Check with `Spikes/check.sh [module.agda ...]` (each module in its own Agda process, under
`formal/scripts/agda-safe.sh`'s memory cap).

Not here: proofs the compiler relies on (those are `formal/`, apex-reachable: no islands), and
exploratory research with no plan behind it.
