#pragma once

#ifdef _MSC_VER
#pragma comment(lib, "Ws2_32.lib")
#pragma comment(lib, "Bcrypt.lib")
#pragma comment(lib, "Userenv.lib")
#endif

extern void compile(const char* source);
