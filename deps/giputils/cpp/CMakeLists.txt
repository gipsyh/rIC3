cmake_minimum_required(VERSION 3.5)
project(giputils)
set(CMAKE_CXX_STANDARD 11)

include_directories(${CMAKE_CURRENT_SOURCE_DIR})
add_library(giputils STATIC giputils.c)

add_custom_target(
    libgiputils
    COMMAND cargo build --release --target-dir ${CMAKE_CURRENT_SOURCE_DIR}/../target
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/..
    DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/../src/*.rs
)
add_dependencies(giputils libgiputils)

target_include_directories(giputils PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(giputils ${CMAKE_CURRENT_SOURCE_DIR}/../target/release/libgiputils.a)
