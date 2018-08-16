# quorum_intersection
A tool for verifying the quorum intersection property of the stellar network. It accepts data in JSON format compatible with https://www.stellarbeat.io/nodes/raw . Use --help parameter to see available options. WARNING: the problem of finding disjoint quorums in stellar's network configuration is NP-hard.
## Getting Started
### Prerequisites
Tools and libraries required to build this project:
* g++ 5.4.0
* boost_graph 1.58.0
* boost_log 1.58.0
* boost_program_options 1.58.0
* cmake 3.5.1
### Build Instructions
```console
mkdir build;
cd build;
cmake ../;
cmake --build .;
```
### Example Session
```
curl "https://www.stellarbeat.io/nodes/raw" | ./quorum_intersection
```
Expected Output:
```console
'true' if all quorums of a given configuration intersect. 'false' otherwise..
```
