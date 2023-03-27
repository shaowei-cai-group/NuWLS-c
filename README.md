# NuWLS-c

NuWLS-c is an incomplete solver designed to solve the MaxSAT problem. 

NuWLS-c won first place in all the categories of the incomplete track in the MaxSAT Evaluation 2022. 

The solver is described in the PDF file located in the doc folder.

## Usage

To run NuWLS-c, execute the script located in the bin folder.

```bash
# using runsolver, cutoff time 300s
./bin/starexec_run_default-runsolver instance-file

# using runsolver, cutoff time 60s
./bin/starexec_run_short-runsolver instance-file
```

## Compilation
To compile the NuWLS-c, please refer to the makefile located in the code folder.
```bash
cd code
make
```
