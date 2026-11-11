#nullable disable
// 从 Il2CppDumper 保留特性数据访问，省去文本导出。
using System.Collections.Generic;
using System.IO;

namespace Il2CppDumper
{
    internal class CustomAttributeDataReader : BinaryReader
    {
        private readonly Il2CppExecutor executor;
        private readonly Metadata metadata;
        private long ctorBuffer;
        private long dataBuffer;

        public uint Count { get; set; }

        public CustomAttributeDataReader(Il2CppExecutor executor, byte[] buff) : base(new MemoryStream(buff))
        {
            this.executor = executor;
            metadata = executor.metadata;
            Count = this.ReadCompressedUInt32();
            ctorBuffer = BaseStream.Position;
            dataBuffer = BaseStream.Position + Count * 4;
        }





        public CustomAttributeReaderVisitor VisitCustomAttributeData()
        {
            var visitor = new CustomAttributeReaderVisitor();

            BaseStream.Position = ctorBuffer;
            var ctorIndex = ReadInt32();
            visitor.CtorIndex = ctorIndex;
            var methodDef = metadata.methodDefs[ctorIndex];
            var typeDef = metadata.typeDefs[methodDef.declaringType];
            ctorBuffer = BaseStream.Position;

            BaseStream.Position = dataBuffer;
            var argumentCount = this.ReadCompressedUInt32();
            var fieldCount = this.ReadCompressedUInt32();
            var propertyCount = this.ReadCompressedUInt32();

            visitor.Arguments = new AttributeArgument[argumentCount];
            for (var i = 0; i < argumentCount; i++)
            {
                var argument = visitor.Arguments[i] = new AttributeArgument();
                argument.Value = ReadAttributeDataValue();
                argument.Index = i;
            }
            visitor.Fields = new AttributeArgument[fieldCount];
            for (var i = 0; i < fieldCount; i++)
            {
                var field = visitor.Fields[i] = new AttributeArgument();
                field.Value = ReadAttributeDataValue();
                (var declaring, var fieldIndex) = ReadCustomAttributeNamedArgumentClassAndIndex(typeDef);
                field.Index = declaring.fieldStart + fieldIndex;
            }
            visitor.Properties = new AttributeArgument[propertyCount];
            for (var i = 0; i < propertyCount; i++)
            {
                var property = visitor.Properties[i] = new AttributeArgument();
                property.Value = ReadAttributeDataValue();
                (var declaring, var propertyIndex) = ReadCustomAttributeNamedArgumentClassAndIndex(typeDef);
                property.Index = declaring.propertyStart + propertyIndex;
            }

            dataBuffer = BaseStream.Position;
            return visitor;
        }

        private BlobValue ReadAttributeDataValue()
        {
            var type = executor.ReadEncodedTypeEnum(this, out var enumType);
            executor.GetConstantValueFromBlob(type, this, out var blobValue);
            if (enumType != null)
            {
                blobValue.EnumType = enumType;
            }
            return blobValue;
        }

        private (Il2CppTypeDefinition, int) ReadCustomAttributeNamedArgumentClassAndIndex(Il2CppTypeDefinition typeDef)
        {
            var memberIndex = this.ReadCompressedInt32();
            if (memberIndex >= 0)
            {
                return (typeDef, memberIndex);
            }
            memberIndex = -(memberIndex + 1);

            var typeIndex = this.ReadCompressedUInt32();
            var declaringClass = metadata.typeDefs[typeIndex];

            return (declaringClass, memberIndex);
        }
    }
}
