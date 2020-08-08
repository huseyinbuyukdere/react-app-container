/// <reference types="react" />
import { MenuItem } from '../../models';
interface HeaderProps {
    leftContent?: any;
    rightContent?: any;
    pageName?: any;
    menu?: MenuItem[];
}
export default function Header(props: HeaderProps): JSX.Element;
export {};
