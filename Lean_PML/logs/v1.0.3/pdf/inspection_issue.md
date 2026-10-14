# PDF 读取过程说明

首次只读检查使用 `pg.get('/Annots', [])` 后对间接对象调用 len，报错：
`TypeError: object of type 'IndirectObject' has no len()`。
该尝试未修改 PDF。随后保存的 inspect_pdf.py 使用 `pg['/Annots']` 解析间接引用，实际运行成功，完整输出见 pdf_inspection 日志。
编辑在本轮完整构建、独立审计及语义核查通过后执行；标记脚本检查源码哈希和被标注声明的审计输出。
