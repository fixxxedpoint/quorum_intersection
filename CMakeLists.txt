cmake_minimum_required (VERSION 2.6)
project (stellar-quorums-verifier)
set(CMAKE_CXX_STANDARD 14)

set(Boost_USE_STATIC_LIBS OFF)
set(Boost_USE_MULTITHREADED OFF)
set(Boost_USE_STATIC_RUNTIME OFF)
find_package(Boost 1.58.0 COMPONENTS graph log program_options REQUIRED)

if(Boost_FOUND)
    add_definitions(-DBOOST_LOG_DYN_LINK)
    include_directories(${Boost_INCLUDE_DIRS})
    add_executable(quorum_intersection quorum_intersection.cpp)
    target_link_libraries(quorum_intersection ${Boost_LIBRARIES})
endif()
