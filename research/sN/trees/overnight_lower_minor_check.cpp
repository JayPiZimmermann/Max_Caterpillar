// Independent scalar finite-field determinant check. No FLINT or rank solver.
// Input: uint64 dimension followed by row-major little-endian uint32 entries.
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>
static constexpr uint64_t P=1000003;
static uint64_t power(uint64_t a,uint64_t k) {
    uint64_t value=1;
    while(k) { if(k&1)value=value*a%P; a=a*a%P;k>>=1; }
    return value;
}
int main(int argc,char**argv) {
 try {
    if(argc!=3)throw std::runtime_error("MINOR_BINARY RECEIPT_JSON");
    auto started=std::chrono::steady_clock::now();
    std::ifstream input(argv[1],std::ios::binary);
    uint64_t n;input.read(reinterpret_cast<char*>(&n),sizeof(n));
    if(!input||n!=1971)throw std::runtime_error("unexpected dimension");
    std::vector<uint32_t>matrix(n*n);
    input.read(reinterpret_cast<char*>(matrix.data()),matrix.size()*sizeof(uint32_t));
    if(!input||input.peek()!=EOF)throw std::runtime_error("wrong matrix size");
    for(auto v:matrix)if(v>=P)throw std::runtime_error("invalid residue");
    uint64_t determinant=1,swaps=0;
    for(uint64_t k=0;k<n;++k) {
        uint64_t pivot=k;
        while(pivot<n&&!matrix[pivot*n+k])++pivot;
        if(pivot==n)throw std::runtime_error("singular minor");
        if(pivot!=k) {
            for(uint64_t j=k;j<n;++j)std::swap(matrix[pivot*n+j],matrix[k*n+j]);
            determinant=P-determinant;++swaps;
        }
        uint64_t value=matrix[k*n+k];
        determinant=determinant*value%P;
        uint64_t inv=power(value,P-2);
        if(value*inv%P!=1)throw std::runtime_error("invalid pivot inverse");
        const uint32_t* row=matrix.data()+k*n;
        for(uint64_t i=k+1;i<n;++i) {
            uint32_t* dest=matrix.data()+i*n;
            uint64_t multiplier=dest[k]*inv%P;
            dest[k]=0;
            if(!multiplier)continue;
            for(uint64_t j=k+1;j<n;++j) {
                uint32_t subtract=multiplier*row[j]%P;
                dest[j]=dest[j]>=subtract?dest[j]-subtract:dest[j]+P-subtract;
            }
        }
        if((k+1)%128==0)std::cout<<"PIVOTS "<<k+1<<" SECONDS "
            <<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<std::endl;
    }
    auto elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
    std::ofstream output(argv[2]);
    output<<"{\n  \"status\": \"NONZERO_AUGMENTED_MINOR_MOD_PRIME\",\n  \"dimension\": "<<n
          <<",\n  \"prime\": "<<P<<",\n  \"determinant\": "<<determinant
          <<",\n  \"row_swaps\": "<<swaps<<",\n  \"seconds\": "<<elapsed<<"\n}\n";
    if(!output||!determinant)throw std::runtime_error("invalid final receipt");
    std::cout<<"PASS DIMENSION "<<n<<" DETERMINANT "<<determinant<<" SECONDS "<<elapsed<<std::endl;
 }catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 1;}
}
