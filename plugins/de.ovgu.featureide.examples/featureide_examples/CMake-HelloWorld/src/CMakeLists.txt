cmake_minimum_required(VERSION 3.5)

option(HELLO_WORLD "Build the print function for [Hello World]." OFF)
option(HELLO_BEAUTIFUL_WORLD "Build the print function for [Hello Beautiful World]." OFF)

add_executable(main main.c)

if(HELLO_WORLD)
    add_library(printHelloWorld printHelloWorld.c)
    target_link_libraries(main printHelloWorld)
endif(HELLO_WORLD)

if(HELLO_BEAUTIFUL_WORLD)
    add_library(printHelloBeautifulWorld printHelloBeautifulWorld.c)
    target_link_libraries(main printHelloBeautifulWorld)
endif()