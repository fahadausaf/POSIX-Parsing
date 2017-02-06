//============================================================================
// Name        : teststrings.cpp
// Author      : Lasse Nielson
//
// Description : Generation of Test Strings for Regular Expressions
//
// Compile     : g++ -o teststrings teststrings.cpp
//============================================================================

#include <iostream>
#include <string>
#include <sstream>

using namespace std;

string str_email(int n) {
	stringstream ss;
	for (int i = 0; i < n; ++i) {
		for (int j = 0; j < i % 27 + 3; ++j)
			ss << (char) ('a' + (j % 26));
		if (n > i + 1)
			ss << "-";
	}
	ss << "@";
	for (int j = 0; j < 2; ++j) {
		for (int i = 0; i < n + 3; ++i)
			ss << (char) ('a' + ((i + j) % 26));
		ss << ".";
	}
	ss << "com";
	return ss.str();
}

string str_amount(int n) {
	stringstream ss;
	ss << "$";
	for (int i = 0; i < n; ++i) {
		ss << (1 + i) % 10;
		if (n > i + 1 && (n - i) % 3 == 1)
			ss << ",";
	}
	ss << ".53";
	return ss.str();
}

string str_float(int n) {
	stringstream ss;
	ss << "-";
	for (int i = 0; i < n; ++i) {
		ss << (1 + i) % 10;
	}
	ss << ".";
	for (int i = 0; i < n; ++i) {
		ss << (1 + i) % 10;
	}
	ss << "E+";
	for (int i = 0; i < n; ++i) {
		ss << (1 + i) % 10;
	}
	return ss.str();
}

int main() {
    
        int fin = 10;

	// emails 
        for (int i = 1; i < fin; i++) {
          cout << str_email(i) << endl;
        }

        // dollar amounts
        for (int i = 1; i < fin; i++) {
	  cout << str_amount(i) << endl;
        }

        // float numbers
        for (int i = 1; i < fin; i++) {
	  cout << str_float(i) << endl;
        }

	return 0;
}
