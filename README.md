# ICFP 2024 Artifact

Name: Contextual Typing

## Step-by-step Instructions

We provide two alternatives: 

1. start from the source code in your local machine, or 
1. use the provided VM with the environment installed.

### Option 1: Build the source locally

We recommend the reviewer to go for this option, based on two reasons:

* This artifact is all about normal Agda, with its standard libraries. It will not bring too much trouble to the environment setup.
* The review of the artifact is mainly about comparing the figures, theorems and proofs between the paper and code. And we provide a script to generate nicely rendered html files. Reviewer is able to review the whole formalisation on their own web browser, once they have finished the compilation.

The author(s) tested the code in a Macbook, so the suggested steps are based on this preference, however, this artifact is expected to work on any platform that supports Agda.

#### Step 1: Install Agda and its standard library

This artifact is supposed to work with recent versions of Agda, we recommend using the latest one (Agda 2.6.4).
We followed this link to install Agda in the VM image: https://agda.readthedocs.io/en/latest/getting-started/installation.html.

The standard library we used is the `agda-stdlib-2.0`, which can be installed following the instructions in this link: https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md.

#### Step 2: Build (Compile) the source

To check the sanity of this artifact, just `cd` to the root folder, then run

```
agda README.agda
```

`README.agda` is the entry point of the whole formalization, type check it successfully means all the theorems shown in the paper should be ok.

#### Step 3: Generate HTML files

We include the pre-generated html files in our source, but the reviewer can delete them and regenerate them by running

```
agda --html README.agda --css "../css/Agda.css"
```

The css file is configured for a nice font and layout.

### Option 2: Use the provided VM

We provide a VM image with the environment installed, and the project source was pre-compiled.

#### Step 1: Start the VM

Unarchive the provided VM image, then run the following command in the terminal:

```
./start.sh
```

This will boot the VM and show the login screen, the default username is `artifact` and the password is `password`.
There are two folders in the home directory: `agda-stdlib` and `icfp`. The `icfp` is the source folder.
Run the following command to type check the agda:

```
cd icfp
agda README.agda
```

The first time it will take several minutes to compile since `agda-stdlib` needs some time.
Since we pre-compiled it, the reviewer should only need to wait for a few seconds.

We also provide the command to generate the html files:

```
agda --html README.agda --css "../css/Agda.css"
```

But it is suggested to run this command in the local machine, to utilize the web browser to view it.

## Correspondence with the paper

The `README.agda` is the entry, which gives the overview of our Agda formalisation.

Roughly, the paper presents several small QTASs in Section 3 and two main calculi in Section 3, 4 and 5.

The several systems are formalized in root folder and two calculi have several own projection folder.

We have tried our best to match the notation from Agda code with the paper, so the Agda script is readable to people with some experience in proof assistant. However, we prove the details about each theorem shown in the paper, to help better review this artifact.

### Bidirectional typing, let-argument-go-first and the corresponding QTASs

| Figure                                    | Agda            | File Location            | Comments (if any)                                            |
| ----------------------------------------- | --------------- | ------------------------ | ------------------------------------------------------------ |
| Fig. 1 Bidirectional typing of STLC       | `_⊢b_#_⦂`_      | AllOrNothing.agda        | Our formorlisation is different from classic bidirecitonal type system (shown in Fig.1), we add a App2 rule and change Lit rule to a inference mode, to better connect to QTASs, which is explained in paper line 420. |
| Fig. 2 Let arguments go first             | `_~_⊢_⇒_`       | Application.agda         | Lit and Var shown in paper are syntactic sugar when application stack is empty, while in Agda we show in expanded version. |
| Fig. 3. STLC with all-or-nothing counters | `_⊢d_#_⦂_`      | AllOrNothing.agda        |                                                              |
| Fig. 4. STLC with application counters    | `_⊢d_#_⦂_`      | Application.agda         |                                                              |
| Fig. 5. All-in-one QTAS                   | `_⊢d_#_⦂_`      | AllInOne.agda            | we have the same judgment defined in `STLC/Decl.agda`        |
| Fig. 6 Typing derivation                  | `ex-derivation` | STLC/Decl.agda           |                                                              |
| Fig. 7 Elaboration rules                  | `_⊢1_⦂_⟶_`      | STLC/Annotatability.agda | `_⊢2_⦂_⟶`_ and `_⊢3_⦂_⟶`_ are two other versions of elaboration rules |


| Theorem                                          | Agda                                                         | File Location            | Comments (if any)                                            |
| ------------------------------------------------ | ------------------------------------------------------------ | ------------------------ | ------------------------------------------------------------ |
| Theorem 3.1 (Soundness)                          | `sound`, `sound-inf`, `sound-chk`                            | AllOrNothing.agda        | sound is the general form, the theorem shown on the paepr are corollaries. |
| Theorem 3.2 (Completeness)                       | `complete`, `complete-inf`, `complete-chk`                   | AllOrNothing.agda        | like above                                                   |
| Theorem 3.3 (Soundness)                          | `sound`                                                      | Application.agda         |                                                              |
| Theorem 3.4 (Completeness)                       | `complete`                                                   | Application.agda         |                                                              |
| Theorem 3.5 (Completeness)                       | `complete`, `complete'`                                      | AllInOne.agda            |                                                              |
| Theorem 3.6 (Weak Annotatability)                | `complete`                                                   | STLC/Annotatability.agda |                                                              |
| Theorem 3.7 (Strong Annotatability)              | `annotatability`, `annotatability'`                          | STLC/Annotatability.agda |                                                              |
| Theorem 3.7 (Strong Annotatability) (Other ver.) | `annotatability2`, `annotatability2'`, `annotatability3`, `annotatability3'` | STLC/Annotatability.agda | As claimed in paper line 650: "Rules EApp2 and EApp3 provide two different alternative annotatability strategies/guidelines" |

### The STLC Calculus

| Figure                                  | Agda                            | File Location    | Comments (if any)                                            |
| --------------------------------------- | ------------------------------- | ---------------- | ------------------------------------------------------------ |
| Fig. 8. Syntax  (part 1)                | `Type`, `Term` and `Env`        | STLC/Common.agda | constructs shared by two systems: QTAS and its algorithmic formulation |
| Fig. 8. Syntax  (part 2)                | `Context` and `GenericConsumer` | STLC/Algo.agda   | contructs specific to Algo. system                           |
| Fig. 9. Algorithmic typing and matching | `_⊢_⇒_⇒_` and `_⊢_≈_`           | STLC/Algo.agda   |                                                              |
| line 544 example                        | `ex2-derivation`                | STLC/Decl.agda   |                                                              |

| Theorem                                | Agda                              | File Location             | Comments (if any)                                |
| -------------------------------------- | --------------------------------- | ------------------------- | ------------------------------------------------ |
| Lemma 4.1 (Typing Implies Matching)    | `⊢to≈`                            | STLC/Algo/Properties.agda |                                                  |
| Lemma 4.2 (A Full Type Context)        | `⊢context-full-type`              | STLC/Algo/Properties.agda |                                                  |
| Lemma 4.3 (General Subsumption)        | `subsumption-0`                   | STLC/Algo/Properties.agda | `subsumption` is the general form                |
| Lemma 4.4 (Decidability of Tatching)   | `≈dec'`                           | STLC/Algo/Decidable.agda  | `≈dec` is the general form                       |
| Lemma 4.5 (Decidability of Typing)     | `⊢dec'`                           | STLC/Algo/Decidable.agda  | `⊢dec` is the general form                       |
| Corollary 4.6 (Soundness of Typing)    | `sound-inf0` and `sound-chk0`     | STLC/Soundness.agda       | `sound-inf` and `sound-chk` are the general form |
| Corollary 4.7 (Completeness of Typing) | `complete-inf` and `complete-chk` | STLC/Completeness.agda    | `complete` is the general form                   |

### The C& Calculus

| Figure                        | Agda                         | File Location         | Comments (if any)                     |
| ----------------------------- | ---------------------------- | --------------------- | ------------------------------------- |
| Fig. 10 Syntax (Part 1)       | `Type`, `Constant`, `Env`    | Record/PreCommon.agda |                                       |
| Fig. 10 Syntax (Part 2)       | `Term`, `Record`             | Record/Common.agda    | Term and records are mutually defined |
| Fig. 10 Syntax (Part 3)       | `CCounter`, `Counter`        | Record/Decl.agda      | check counter and counters            |
| Fig. 10 Syntax (Part 4)       | `Context`, `GenericConsumer` | Record/Algo.agda      |                                       |
| Fig. 11 QTAS typing           | `_⊢_#_⦂_`, `_⊢r_#_⦂_`        | Record/Decl.agda      | `r` stands for records                |
| Fig. 11 QTAS subtyping        | `_≤_#_`                      | Record/Decl.agda      |                                       |
| Example (line 1023 and  1053) | `ex-overloading`             | Record/Decl.agda      |                                       |
| Fig. 12 Algo. Typing          | `_⊢_⇒_⇒_`, `_⊢r_⇒_⇒_`        | Record/Algo.agda      |                                       |
| Fig. 12 Algo. Subtyping       | `⊢_≤_⇝_`                     | Record/Algo.agda      |                                       |

| Theorem                                         | Agda                                                    | File Location                          | Comments (if any) |
| ----------------------------------------------- | ------------------------------------------------------- | -------------------------------------- | ----------------- |
| Lemma 5.1 (Reflexivity of Subtyping (Infinity)) | `≤refl∞`                                                | Record/Decl.agda                       |                   |
| Lemma 5.2 (Transitivity of Subtyping)           | `≤trans`                                                | Record/Decl/Properties.agda            |                   |
| Lemma 5.3 (A full type context) typing          | `⊢id-0`                                                 | Record/Algo/Properties.agda            |                   |
| Lemma 5.4 (A full type context) subtyping       | `≤id-0`                                                 | Record/Algo/Properties.agda            |                   |
| Lemma 5.5 (Typing implies subtyping)            | `⊢to-≤`                                                 | Record/Algo/Properties.agda            |                   |
| Lemma 5.6 (General Subsumption)                 | `subsumption-0`                                         | Record/Algo/Properties.agda            |                   |
| Corollary 5.7 (Soundness of Typing)             | `sound-inf-0`, `sound-chk-0`, `sound-r`                 | Record/Soundness.agda                  |                   |
| Corollary 5.8 (Completeness of Typing)          | `complete-inf`, `complete-chk`, `complete-r`            | Record/Completeness.agda               |                   |
| Theorem 5.9 (Strong Annotatability)             | `annotatability`, `annotatability'`, `annotatability-r` | Record/Annotatability/Elaboration.agda |                   |
| Theorem 5.10 (Type preservation after erasure)  | `preserve`, `preserve-r`                                | TypeSound/Main.agda                    |                   |
| Theorem 5.11 (Preservation of TAS)              | `preserve`, `preserve-r`                                | TypeSound/Target.agda                  |                   |
| Theorem 5.12 (Progress of TAS)                  | `progress`, `progress-r`                                | TypeSound/Target.agda                  |                   |
| Lemma 5.13 (Determinism of Typing)              | `⊢unique`, `⊢r-unique`                                  | Record/Algo/Uniqueness.agda            |                   |
| Lemma 5.14 (Determinism of Subtyping)           | `≤unique`                                               | Record/Algo/Uniqueness.agda            |                   |
| Theorem 5.15 (Decidability of Typing)           | `⊢dec-0`, `⊢r-dec`                                      | Record/Algo/Decidable.agda             |                   |
| Theorem 5.16 (Decidability of Subtyping)        | `≤dec-0`                                                | Record/Algo/Decidable.agda             |                   |
| Corollary 5.17 (Decidability of the QTAS)       | `qtas-dec-0`                                            | Record/Dec.agda                        |                   |

## QEMU Instructions

The ICFP 2024 Artifact Evaluation Process is using a Debian QEMU image as a
base for artifacts. The Artifact Evaluation Committee (AEC) will verify that
this image works on their own machines before distributing it to authors.
Authors are encouraged to extend the provided image instead of creating their
own. If it is not practical for authors to use the provided image then please
contact the AEC co-chairs before submission.

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

### Artifact Preparation

Authors should install software dependencies into the VM image as needed,
preferably via the standard Debian package manager. For example, to install
GHC and cabal-install, login to the host and type:

```
$ sudo apt update
$ sudo apt install ghc
$ sudo apt install cabal-install
```

If you really need a GUI then you can install X as follows, but we prefer
console-only artifacts whenever possible.

```
$ sudo apt install xorg
$ sudo apt install xfce4   # or some other window manager
$ startx
```

See Debugging.md for advice on resolving other potential problems.

If your artifact needs lots of memory you may need to increase the value
of the `QEMU_MEM_MB` variable in the `start.sh` script.

When preparing your artifact, please also follow the [Submission
Guidelines](https://icfp24.sigplan.org/track/icfp-2024-artifact-evaluation#Submission-Guidelines).
