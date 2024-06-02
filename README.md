# ICFP 2024 Artifact

Name:    **Story of Your Lazy Function’s Life: A Bidirectional Demand Semantics for Mechanized Cost Analysis of Lazy Programs**

## Project overview and relation to the paper

- Approximation data types are defined in
- General notions relating to approximations are defined in `Approx.v`.
  + The typeclass `LessDefined` represents the lattice of approximations itself: an instance `LessDefined A` defines the approximation relation, called `less_defined` in Coq, for the type `A`.  The paper states facts about this relation (e.g., transitivity) as lemmas; however, in Coq, these lemmas must be proven for each instance.
  + The `Exact` typeclass shows how to embed a type into its type of approximations (via the `exact` method).  The `ExactMaximal` typeclass is a law for `Exact`: it says that an embedded value should be maximal with respect to `less_defined`.  We *define* the "approximates" relation `is_approx` (denoted ≺ in the paper) by saying that a value `xD` approximates `x` if `xD` is less defined than `exact x`; i.e., `xD` lies below `exact x` in the lattice of approximations.
  +
- The clairvoyance semantics of Hackett and Hutchinson are formalized in `Core.v`.  The clairvoyance monad itself is called `M`

### Major proof terms

- Insertion sort (`InsertionSort.v`):
  + Functional correctness: `insertion_sortD__approx`
  + Cost: `insertion_sortD_cost`
  + Cost when composed with `take`: `take_insertion_sortD_cost`
- Banker's queue:
  + Functional correctness (`BankersQueue.v`):
    * `mkQueueD_approx`
    * `pushD_approx`
    * `popD_approx`
  + Equivalence with clairvoyance semantics (`BankersQueue.v`):
    * `mkQueueD_spec`
    * `pushD_spec`
    * `popD_spec`
  + Amortized cost (`QueueInterface.v`): `amortized_cost`
- Implicit queue (`ImplicitQueue.v`):
  + Functional correctness:
    * `emptyD_approx`
    * `pushD_apporox`
    * `popD_approx`
  + Equivalence with clairvoyance semantics:
    * `emptyD_spec`
    * `pushD_spec`
    * `popD_spec`
  + Amortized cost: `amortized_cost`

## Artifact Instructions

The project lives in the `demand-semantics` directory under the home directory of the default `artifact` user.  (Whenever a password is required, enter `password`).  The image already has all dependencies installed; to execute the proof scripts, you just need to run `make`.

### Dependencies

The project is known to work with Coq versions 8.16.1 and 8.17.1.  You also need the following Coq libraries and plugins:

- [Equations](https://github.com/mattam82/Coq-Equations)
- [CoqHammer](https://github.com/lukaszcz/coqhammer) (only the `sauto` component is needed)

Both of these components are part of the [Coq platform](https://github.com/coq/platform).

### Checking axioms

To check the axioms of a named proof term, use the command `Print Assumptions [name]`.  When you check the major proof terms, you should see only the axiom `Classical_Prop.classic`, which is the law of excluded middle.

## QEMU Instructions

QEMU is a hosted virtual machine monitor that can emulate a host processor
via dynamic binary translation. On common host platforms QEMU can also use
a host provided virtualization layer, which is faster than dynamic binary
translation.

QEMU homepage: https://www.qemu.org/

### Installation

#### OSX
``brew install qemu``

#### Debian and Ubuntu Linux
``apt-get install qemu-kvm``

On x86 laptops and server machines you may need to enable the
"Intel Virtualization Technology" setting in your BIOS, as some manufacturers
leave this disabled by default. See Debugging.md for details.


#### Arch Linux

``pacman -Sy qemu``

See the [Arch wiki](https://wiki.archlinux.org/title/QEMU) for more info.

See Debugging.md if you have problems logging into the artifact via SSH.


#### Windows 10

Download and install QEMU via the links at

https://www.qemu.org/download/#windows.

Ensure that `qemu-system-x86_64.exe` is in your path.

Start Bar -> Search -> "Windows Features"
          -> enable "Hyper-V" and "Windows Hypervisor Platform".

Restart your computer.

#### Windows 8

See Debugging.md for Windows 8 install instructions.

### Startup

The base artifact provides a `start.sh` script to start the VM on unix-like
systems and `start.bat` for Windows. Running this script will open a graphical
console on the host machine, and create a virtualized network interface.
On Linux you may need to run with `sudo` to start the VM. If the VM does not
start then check `Debugging.md`

Once the VM has started you can login to the guest system from the host.
Whenever you are asked for a password, the answer is `password`. The default
username is `artifact`.

```
$ ssh -p 5555 artifact@localhost
```

You can also copy files to and from the host using scp.

```
$ scp -P 5555 artifact@localhost:somefile .
```

### Shutdown

To shutdown the guest system cleanly, login to it via ssh and use

```
$ sudo shutdown now
```
